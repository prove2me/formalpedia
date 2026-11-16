-- Prove2me | Theorems.Thm_MeanBudgetXC_Supplement_theorem_5_9
-- name    : MeanBudgetXC.Supplement.theorem_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:15:56.559084+00:00
-- url     : https://prove2.me/theorems/66674543-5b63-483d-a199-87caf75083c4
-- title:
--   Theorem 5.9 — size lower bounds for positive surplus, uniform in $a$ and $B$, and $s_E+m_E+2\ge2^{c_IN^\kappa}$ for the section $Z_B$
-- statement:
--   Notation. Write $M=\binom N2$ for the number of pair coordinates $q_{ij}$ ($i<j$), $P^{(a)}_{N,d}$ for the pair body of consistent local laws on all contexts of size at most $d$ with at most $a$ ones, and $P^{(a;B)}_{N,d}$ for its subset of arrays coming from a system with mean budget $\sum_ip_i\le B$; $P=P^{(2)}_{N,d}$ and $P_B=P^{(2;B)}_{N,d}$. For a set $A$ of pair arrays and a cap $u\ge0$, the **capped value** is
--   $$V_A(u)=\max\{1^{\mathsf T}q:\ q\in A,\ 0\le q\le u\}.$$
--   A **common LP** is a linear system with $s$ inequalities (equations and auxiliary variables free, real coefficients) projecting onto an output polyhedron $K$; it is fixed before the cap, each query adds the cap $0\le q\le u$ directly on the output, and its error at $u$ is $|V_K(u)-V_{\text{target}}(u)|$ (Section 1.3).
--
--   There is an absolute $\kappa>0$ (the exponent of Theorem 5.2) such that for every closed interval $I=[\theta_0,\theta_1]\subset(0,1)$ there are constants $\epsilon_I,c_I>0$ and a threshold $N_0$ with the following property. For all integers $N\ge N_0$ and $d$ with $d/N\in I$ there is a triangle-free host graph $Q$ on the $N$ variables with $d-1\ge2\Delta(Q)$ and $m_E=|E(Q)|$ edges (the constructed common host) such that:
--
--   1. for every integer $a\ge2$ and every $B>2$, any common LP with $s_{\mathrm{raw}}$ inequalities whose capped sets are nonempty at every cap in $[0,1]^M$ and whose additive error for $P^{(a;B)}_{N,d}$ is at most $\epsilon_I\min\{B-2,1\}$ at every cap in $[0,1]^M$ satisfies
--   $$s_{\mathrm{raw}}+2M+2m_E+3\ge2^{c_IN^\kappa};$$
--   if the output already lies in $[0,1]^M$, the $2M$ term is omitted;
--   2. for every $B>2$, an exact $s_E$-inequality lift of the constructed section $Z_B=\{x\in\mathbb R^{E(Q)}_{\ge0}: c_S\cdot x\le1\ (|S|=d),\ \sum_ex_e\le B/2\}$ satisfies
--   $$s_E+m_E+2\ge2^{c_IN^\kappa};\tag{36}$$
--   3. for every $B>2$, every positive scaling $tZ_B$ ($t>0$) has the same exact extension complexity as $Z_B$.
--
--   All constants and thresholds are independent of $a$ and $B$, including $N$-dependent $B>2$.
--
--   Differences from the source:
--   - encoding: the vertex set $[N]$ → `Fin N`; reason: the same set, indexed from zero
--   - encoding: a common LP (base formulation) with $s$ inequalities and output polyhedron $K$ → `IsEFOfSize K s` (platform); reason: the paper's counting convention (p.4, App. A.1): inequalities counted, equations and auxiliary variables free, real coefficients, unbounded lifts allowed
--   - encoding: $V_A(u)=\max\{1^{\mathsf T}q: q\in A,\ 0\le q\le u\}$ → `capValue A u`, the supremum of $\sum_e q_e$ over the capped set; reason: the capped set is nonempty and lies in the box $[0,u]$, and $A$ is a polyhedron or a compact body, so the supremum is attained and equals the maximum
--   - encoding: nonempty capped feasible sets and finite values → nonempty capped sets only; reason: the capped set lies in the box $[0,u]$, so the value is always finite; the finiteness hypothesis excludes nothing
--   - reading: "the constructed common triangle-free host $Q$" with $m_E=|E(Q)|$ → an existential triangle-free graph $Q$ on the $N$ variables with $d-1\ge2\Delta(Q)$, chosen after $N$ (and $d$) and before $a$, $B$ and the LP, with $m_E$ its number of edges; reason: the host of Section 5.4 and Appendix C.3 is built from existentially chosen data (the graph $H^*$ of Lemma 5.3, the padding graph $T$ of Appendix C.1); these are the properties the paper states for it ((25), p.24; Appendix C.3); $m_E$ is kept, not replaced by $M$
--   - reading: $\kappa$ is the exponent of Theorem 5.2 → an absolute $\kappa>0$ quantified first, before every other constant; reason: each statement is standalone; Theorem 5.2 fixes $\kappa$ only as an absolute positive constant
--   - encoding: a closed interval $I\subset(0,1)$, $d/N\in I$ → $I=[\theta_0,\theta_1]$ with $0<\theta_0\le\theta_1<1$ and $\theta_0\le d/N\le\theta_1$ in $\mathbb R$; reason: a closed subinterval of $(0,1)$ is exactly such an $[\theta_0,\theta_1]$
--   - encoding: the constructed section $Z_B=Z\cap\{W\le B/2\}$ of (33) → the published `budgetZeroSection Q d B`; reason: the same set
--   - encoding: every positive scaling of $Z_B$ has the same exact extension complexity → `extensionComplexity (t • Z_B) = extensionComplexity Z_B` for every $t>0$; reason: the platform's extension complexity is the paper's $\mathrm{xc}$
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Theorem 5.9, p.28; host from Section 5.4 and Appendix C.3; $Z_B$ from (33), p.27

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_MeanBudgetXC_budgetBody
import Definitions.Def_MeanBudgetXC_budgetZeroSection
import Definitions.Def_LinfContractionFP_unitCube
import Definitions.Def_MeanBudgetXC_Supplement_capValue

namespace MeanBudgetXC.Supplement

open ExtensionComplexity.TSP Pointwise

/-- **Theorem 5.9** (Size lower bounds for positive surplus) (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Theorem 5.9, p.28). For a fixed closed interval `I ⊂ (0, 1)` there are constants
`ϵ_I, c_I > 0` and a uniform large-`N` threshold such that, for every pair of integers `N, d` with
`d/N ∈ I`, every integer `a ≥ 2`, and every `B > 2`, any common LP whose capped sets are nonempty,
whose values are finite, and whose additive error for `P^{(a;B)}_{N,d}` is at most
`ϵ_I min{B − 2, 1}` for every cap in `[0, 1]^M` satisfies `s_raw + 2M + 2m_E + 3 ≥ 2^{c_I N^κ}`. If
the output already lies in `[0, 1]^M`, the `2M` term is omitted. Moreover, an exact
`s_E`-inequality lift of the constructed section `Z_B` itself satisfies `s_E + m_E + 2 ≥ 2^{c_I N^κ}`
(36). All constants and thresholds are independent of `a` and `B`, including `N`-dependent
`B > 2`. Every positive scaling of `Z_B` has the same exact extension complexity.

**Formalization Note** `I = [θ₀, θ₁]` with `0 < θ₀ ≤ θ₁ < 1`; `κ` is the absolute exponent of
Theorem 5.2, chosen first. The common host `Q` of Section 5.4 / Appendix C.3 is built from
existentially chosen data, so it is stated existentially: a triangle-free graph on the `N`
variables with `d − 1 ≥ 2Δ(Q)`, chosen after `N, d` and before `a`, `B` and the LP;
`m_E = |E(Q)|`. `Z_B = Z ∩ {W ≤ B/2}` of (33), p.27, is the published `budgetZeroSection Q d B`.
The LP is `IsEFOfSize K s` with `K` arbitrary; finite values are automatic. -/
theorem theorem_5_9 :
    ∃ κ : ℝ, 0 < κ ∧ ∀ θ₀ θ₁ : ℝ, 0 < θ₀ → θ₀ ≤ θ₁ → θ₁ < 1 →
      ∃ ϵ c : ℝ, 0 < ϵ ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ d : ℕ,
        θ₀ ≤ (d : ℝ) / N → (d : ℝ) / N ≤ θ₁ →
        ∃ (Q : SimpleGraph (Fin N)) (_ : DecidableRel Q.Adj),
          Q.CliqueFree 3 ∧ 2 * Q.maxDegree ≤ d - 1 ∧
          (∀ B : ℝ, 2 < B →
            (∀ sE : ℕ, IsEFOfSize (budgetZeroSection Q d B) sE →
              (2 : ℝ) ^ (c * (N : ℝ) ^ κ) ≤ sE + Q.edgeFinset.card + 2) ∧
            ∀ t : ℝ, 0 < t →
              extensionComplexity (t • budgetZeroSection Q d B) =
                extensionComplexity (budgetZeroSection Q d B)) ∧
          ∀ a : ℕ, 2 ≤ a → ∀ B : ℝ, 2 < B →
            ∀ (K : Set (Pair (Fin N) → ℝ)) (s : ℕ), IsEFOfSize K s →
              (∀ u ∈ LinfContractionFP.unitCube (Pair (Fin N)), (cappedSet K u).Nonempty) →
              (∀ u ∈ LinfContractionFP.unitCube (Pair (Fin N)),
                |capValue K u - capValue (budgetBody (Fin N) d a B) u| ≤ ϵ * min (B - 2) 1) →
              (2 : ℝ) ^ (c * (N : ℝ) ^ κ) ≤ s + 2 * N.choose 2 + 2 * Q.edgeFinset.card + 3 ∧
              (K ⊆ LinfContractionFP.unitCube (Pair (Fin N)) →
                (2 : ℝ) ^ (c * (N : ℝ) ^ κ) ≤ s + 2 * Q.edgeFinset.card + 3) := by sorry

end MeanBudgetXC.Supplement
