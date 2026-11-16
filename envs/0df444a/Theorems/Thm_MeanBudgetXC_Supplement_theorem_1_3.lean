-- Prove2me | Theorems.Thm_MeanBudgetXC_Supplement_theorem_1_3
-- name    : MeanBudgetXC.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:13:49.017988+00:00
-- url     : https://prove2.me/theorems/96c6bacc-4f6f-493c-be34-a8377a778692
-- title:
--   Theorem 1.3 — error $\le\frac{N-1}{2(d-1)}\gamma$ above budget two, and no polynomial-size common LP beats $\Omega_\theta(\gamma)$
-- statement:
--   Notation. Write $M=\binom N2$ for the number of pair coordinates $q_{ij}$ ($i<j$), $P^{(a)}_{N,d}$ for the pair body of consistent local laws on all contexts of size at most $d$ with at most $a$ ones, and $P^{(a;B)}_{N,d}$ for its subset of arrays coming from a system with mean budget $\sum_ip_i\le B$; $P=P^{(2)}_{N,d}$ and $P_B=P^{(2;B)}_{N,d}$. For a set $A$ of pair arrays and a cap $u\ge0$, the **capped value** is
--   $$V_A(u)=\max\{1^{\mathsf T}q:\ q\in A,\ 0\le q\le u\}.$$
--   A **common LP** is a linear system with $s$ inequalities (equations and auxiliary variables free, real coefficients) projecting onto an output polyhedron $K$; it is fixed before the cap, each query adds the cap $0\le q\le u$ directly on the output, and its error at $u$ is $|V_K(u)-V_{\text{target}}(u)|$ (Section 1.3).
--
--   1. For every $3\le d\le N$, every $\gamma>0$ and every nonnegative cap $u$,
--   $$0\le V_{P_{2+\gamma}}(u)-V_{P_2}(u)\le\frac{N-1}{2(d-1)}\gamma.$$
--   2. Conversely, fix $\theta\in(0,1)$ and put $d=\lfloor\theta N\rfloor$. There is $\epsilon_\theta>0$ such that for all $C>0$ and $r\ge0$ the following holds for all sufficiently large $N$ and every $0<\gamma\le1$: every common LP with at most $CN^r$ rows whose capped feasible sets are nonempty at every query $u\in[0,1]^M$ has a query $u\in[0,1]^M$ whose error for $P_{2+\gamma}$ exceeds $\epsilon_\theta\gamma$:
--   $$|V_K(u)-V_{P_{2+\gamma}}(u)|>\epsilon_\theta\gamma.$$
--   The threshold on $N$ may depend on $C,r,\theta$, but is independent of $\gamma$.
--
--   The first part says that the quadratic-size formulation of $P_2$ (Theorem 1.1) answers capacity queries on $P_{2+\gamma}$ with error $O_\theta(\gamma)$; the second that this order is optimal for every family of LPs with a fixed polynomial row bound.
--
--   **Formalization Note** The rows of a common LP are the $s$ inequalities of its base formulation; the output polyhedron $K$ is arbitrary (not assumed inside $[0,1]^M$, nor to contain the target).
--
--   Differences from the source:
--   - encoding: the vertex set $[N]$ → `Fin N`; reason: the same set, indexed from zero
--   - encoding: a common LP (base formulation) with $s$ inequalities and output polyhedron $K$ → `IsEFOfSize K s` (platform); reason: the paper's counting convention (p.4, App. A.1): inequalities counted, equations and auxiliary variables free, real coefficients, unbounded lifts allowed
--   - encoding: $V_A(u)=\max\{1^{\mathsf T}q: q\in A,\ 0\le q\le u\}$ → `capValue A u`, the supremum of $\sum_e q_e$ over the capped set; reason: the capped set is nonempty and lies in the box $[0,u]$, and $A$ is a polyhedron or a compact body, so the supremum is attained and equals the maximum
--   - encoding: nonempty capped feasible sets and finite values → nonempty capped sets only; reason: the capped set lies in the box $[0,u]$, so the value is always finite; the finiteness hypothesis excludes nothing
--   - reading: "exceeds $\epsilon_\theta\gamma$", with $\epsilon_\theta$ not restated → $\exists\,\epsilon_\theta>0$ chosen after $\theta$ and before $C$, $r$, $N$, $\gamma$ and the LP; reason: the subscript says $\epsilon_\theta$ depends on $\theta$ only (it is the constant of Theorem 1.2); the standalone statement quantifies it
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Theorem 1.3, p.5

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_MeanBudgetXC_budgetBody
import Definitions.Def_LinfContractionFP_unitCube
import Definitions.Def_MeanBudgetXC_Supplement_capValue

namespace MeanBudgetXC.Supplement

open ExtensionComplexity.TSP

/-- **Theorem 1.3** (Optimal order of accuracy above budget two) (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Theorem 1.3, p.5). For every `3 ≤ d ≤ N`, `γ > 0`, and nonnegative cap `u`,
`0 ≤ V_{P_{2+γ}}(u) − V_{P_2}(u) ≤ (N − 1)/(2(d − 1)) · γ`.
Conversely, fix `θ ∈ (0, 1)`, put `d = ⌊θN⌋`, and fix `C > 0` and `r ≥ 0`. For all sufficiently
large `N` and every `0 < γ ≤ 1`, every common LP with at most `C N^r` rows has a query
`u ∈ [0, 1]^M` whose error for `P_{2+γ}` exceeds `ϵ_θ γ`, provided all these queries have nonempty
capped feasible sets and finite values. The threshold on `N` may depend on `C, r, θ`, but is
independent of `γ`.

**Formalization Note** `P_B = budgetBody (Fin N) d 2 B` (activity two). A common LP is a base
formulation of its output polyhedron `K`, `IsEFOfSize K s`, whose `s` inequalities are its rows;
`K` is arbitrary (Section 1.3: no containment of the target, no downward closure, not assumed
inside `[0,1]^M`). The error at `u` is `|V_K(u) − V_{P_{2+γ}}(u)|`. `ϵ_θ` is chosen after `θ` and
before `C, r`; the threshold `N₀` after `C, r` and before `γ` and the LP. Finite values are
automatic, so only nonemptiness of the capped sets is assumed. -/
theorem theorem_1_3 :
    (∀ N d : ℕ, 3 ≤ d → d ≤ N → ∀ γ : ℝ, 0 < γ → ∀ u : Pair (Fin N) → ℝ, 0 ≤ u →
      0 ≤ capValue (budgetBody (Fin N) d 2 (2 + γ)) u - capValue (budgetBody (Fin N) d 2 2) u ∧
        capValue (budgetBody (Fin N) d 2 (2 + γ)) u - capValue (budgetBody (Fin N) d 2 2) u ≤
          ((N : ℝ) - 1) / (2 * ((d : ℝ) - 1)) * γ) ∧
    ∀ θ : ℝ, 0 < θ → θ < 1 → ∃ ϵ : ℝ, 0 < ϵ ∧ ∀ C : ℝ, 0 < C → ∀ r : ℝ, 0 ≤ r →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
        ∀ (K : Set (Pair (Fin N) → ℝ)) (s : ℕ), IsEFOfSize K s → (s : ℝ) ≤ C * (N : ℝ) ^ r →
          (∀ u ∈ LinfContractionFP.unitCube (Pair (Fin N)), (cappedSet K u).Nonempty) →
          ∃ u ∈ LinfContractionFP.unitCube (Pair (Fin N)),
            ϵ * γ < |capValue K u - capValue (budgetBody (Fin N) ⌊θ * N⌋₊ 2 (2 + γ)) u| := by sorry

end MeanBudgetXC.Supplement
