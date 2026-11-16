-- Prove2me | Theorems.Thm_MeanBudgetXC_Supplement_theorem_5_7
-- name    : MeanBudgetXC.Supplement.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:15:12.820208+00:00
-- url     : https://prove2.me/theorems/219cf915-ff9e-4005-834f-c0dde39c3c61
-- title:
--   Theorem 5.7 — size lower bound $s_{\mathrm{raw}}+2M+2m_E+3\ge2^{c_\theta N^\kappa}$ for constant error
-- statement:
--   Notation. Write $M=\binom N2$ for the number of pair coordinates $q_{ij}$ ($i<j$), $P^{(a)}_{N,d}$ for the pair body of consistent local laws on all contexts of size at most $d$ with at most $a$ ones, and $P^{(a;B)}_{N,d}$ for its subset of arrays coming from a system with mean budget $\sum_ip_i\le B$; $P=P^{(2)}_{N,d}$ and $P_B=P^{(2;B)}_{N,d}$. For a set $A$ of pair arrays and a cap $u\ge0$, the **capped value** is
--   $$V_A(u)=\max\{1^{\mathsf T}q:\ q\in A,\ 0\le q\le u\}.$$
--   A **common LP** is a linear system with $s$ inequalities (equations and auxiliary variables free, real coefficients) projecting onto an output polyhedron $K$; it is fixed before the cap, each query adds the cap $0\le q\le u$ directly on the output, and its error at $u$ is $|V_K(u)-V_{\text{target}}(u)|$ (Section 1.3).
--
--   There is an absolute $\kappa>0$ (the exponent of Theorem 5.2) such that for every fixed $\theta\in(0,1)$ there are $\epsilon_\theta,c_\theta>0$ and $N_\theta$ with the following property for every integer $N\ge N_\theta$, with $d=\lfloor\theta N\rfloor$. There is a triangle-free host graph $Q$ on the $N$ variables with $d-1\ge2\Delta(Q)$ and $m_E=|E(Q)|$ edges (the constructed common host) such that for every integer $a\ge2$: let $K$ be the output polyhedron of a common LP with $s_{\mathrm{raw}}$ inequalities and arbitrary real coefficients, suppose all caps $u\in[0,1]^M$ give nonempty capped feasible sets, and $|V_K(u)-V_{P^{(a)}_{N,d}}(u)|\le\epsilon_\theta$ for every such $u$. Then
--   $$s_{\mathrm{raw}}+2M+2m_E+3\ge2^{c_\theta N^\kappa}.\tag{32}$$
--   If $K\subseteq[0,1]^M$, a lift of $K$ with $s$ inequalities satisfies $s+2m_E+3\ge2^{c_\theta N^\kappa}$. In either case $s_{\mathrm{raw}}\ge2^{c'_\theta N^\kappa}$ for a constant $c'_\theta>0$ and all sufficiently large $N$.
--
--   This is the unbudgeted half of Theorem 1.2 with explicit inequality counts.
--
--   Differences from the source:
--   - encoding: the vertex set $[N]$ → `Fin N`; reason: the same set, indexed from zero
--   - encoding: a common LP (base formulation) with $s$ inequalities and output polyhedron $K$ → `IsEFOfSize K s` (platform); reason: the paper's counting convention (p.4, App. A.1): inequalities counted, equations and auxiliary variables free, real coefficients, unbounded lifts allowed
--   - encoding: $V_A(u)=\max\{1^{\mathsf T}q: q\in A,\ 0\le q\le u\}$ → `capValue A u`, the supremum of $\sum_e q_e$ over the capped set; reason: the capped set is nonempty and lies in the box $[0,u]$, and $A$ is a polyhedron or a compact body, so the supremum is attained and equals the maximum
--   - encoding: nonempty capped feasible sets and finite values → nonempty capped sets only; reason: the capped set lies in the box $[0,u]$, so the value is always finite; the finiteness hypothesis excludes nothing
--   - reading: "the constructed common triangle-free host $Q$" with $m_E=|E(Q)|$ → an existential triangle-free graph $Q$ on the $N$ variables with $d-1\ge2\Delta(Q)$, chosen after $N$ (and $d$) and before $a$, $B$ and the LP, with $m_E$ its number of edges; reason: the host of Section 5.3.2 is built from existentially chosen data (the graph $H^*$ of Lemma 5.3, the padding graph $T$ of Appendix C.1); these are the properties the paper states for it ((25), p.24; Appendix C.3); $m_E$ is kept, not replaced by $M$
--   - reading: $\kappa$ is the exponent of Theorem 5.2 → an absolute $\kappa>0$ quantified first, before every other constant; reason: each statement is standalone; Theorem 5.2 fixes $\kappa$ only as an absolute positive constant
--   - reading: $s_{\mathrm{raw}}\ge2^{\Omega_\theta(N^\kappa)}$ for all sufficiently large $N$ → a constant $c'>0$ depending on $\theta$ only with $s\ge2^{c'N^\kappa}$; reason: the subscript $\theta$ fixes what the constant may depend on
--   - encoding: threshold $N_\theta$ for (32) and the $K\subseteq[0,1]^M$ clause, "sufficiently large $N$" for the last clause → one threshold for all three; reason: each clause is monotone in the threshold, so one threshold (the larger) is equivalent
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Theorem 5.7, p.26; host from Section 5.3.2, pp.23–24

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_MeanBudgetXC_pairBody
import Definitions.Def_LinfContractionFP_unitCube
import Definitions.Def_MeanBudgetXC_Supplement_capValue

namespace MeanBudgetXC.Supplement

open ExtensionComplexity.TSP

/-- **Theorem 5.7** (A size lower bound for constant error) (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Theorem 5.7, p.26). For every fixed `θ ∈ (0, 1)` there are `ϵ_θ, c_θ > 0` and `N_θ` such that
the following holds for every integer `N ≥ N_θ` and every integer `a ≥ 2`, with `d = ⌊θN⌋`. Let
`K` be the output polyhedron of a common LP with `s_raw` inequalities and arbitrary real
coefficients. Suppose all caps `u ∈ [0, 1]^M` give nonempty capped feasible sets and finite
values, and `|V_K(u) − V_{P^{(a)}_{N,d}}(u)| ≤ ϵ_θ` for every such `u`. Then the constructed common
triangle-free host `Q` satisfies `s_raw + 2M + 2m_E + 3 ≥ 2^{c_θ N^κ}` (32). If `K ⊆ [0, 1]^M`, a lift
of `K` with `s` inequalities satisfies `s + 2m_E + 3 ≥ 2^{c_θ N^κ}`. In either case
`s_raw ≥ 2^{Ω_θ(N^κ)}` for all sufficiently large `N`.

**Formalization Note** `κ` is the absolute exponent of Theorem 5.2, chosen first. The host `Q`
of Section 5.3.2 (pp.23–24) is built from existentially chosen data (the graph `H∗` of Lemma 5.3,
the padding graph `T` of Appendix C.1), so it is stated existentially: a triangle-free graph on the
`N` variables with `d − 1 ≥ 2Δ(Q)` ((25), p.24), chosen after `N` and before `a` and the LP;
`m_E = |E(Q)|`, `M = (N choose 2)`. `s_raw ≥ 2^{Ω_θ(N^κ)}` is read as a constant `c' > 0` depending
on `θ` only; the three conclusions share one threshold `N_θ` (taking the larger of two thresholds
changes nothing). The LP is `IsEFOfSize K s`; finite values are automatic. -/
theorem theorem_5_7 :
    ∃ κ : ℝ, 0 < κ ∧ ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∃ ϵ c c' : ℝ, 0 < ϵ ∧ 0 < c ∧ 0 < c' ∧ ∃ Nθ : ℕ, ∀ N ≥ Nθ,
        ∃ (Q : SimpleGraph (Fin N)) (_ : DecidableRel Q.Adj),
          Q.CliqueFree 3 ∧ 2 * Q.maxDegree ≤ ⌊θ * N⌋₊ - 1 ∧
          ∀ a : ℕ, 2 ≤ a →
            ∀ (K : Set (Pair (Fin N) → ℝ)) (s : ℕ), IsEFOfSize K s →
              (∀ u ∈ LinfContractionFP.unitCube (Pair (Fin N)), (cappedSet K u).Nonempty) →
              (∀ u ∈ LinfContractionFP.unitCube (Pair (Fin N)),
                |capValue K u - capValue (pairBody (Fin N) ⌊θ * N⌋₊ a) u| ≤ ϵ) →
              (2 : ℝ) ^ (c * (N : ℝ) ^ κ) ≤ s + 2 * N.choose 2 + 2 * Q.edgeFinset.card + 3 ∧
              (K ⊆ LinfContractionFP.unitCube (Pair (Fin N)) →
                (2 : ℝ) ^ (c * (N : ℝ) ^ κ) ≤ s + 2 * Q.edgeFinset.card + 3) ∧
              (2 : ℝ) ^ (c' * (N : ℝ) ^ κ) ≤ s := by sorry

end MeanBudgetXC.Supplement
