-- Prove2me | Theorems.Thm_MeanBudgetXC_Supplement_theorem_1_2
-- name    : MeanBudgetXC.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:13:11.286012+00:00
-- url     : https://prove2.me/theorems/3c509d8b-c8e4-4b7e-aff0-4aeae869fafc
-- title:
--   Theorem 1.2 — capacity lower bound $2^{c_\theta N^\kappa}$ for arbitrary common LPs in $[0,1]^M$
-- statement:
--   Notation. Write $M=\binom N2$ for the number of pair coordinates $q_{ij}$ ($i<j$), $P^{(a)}_{N,d}$ for the pair body of consistent local laws on all contexts of size at most $d$ with at most $a$ ones, and $P^{(a;B)}_{N,d}$ for its subset of arrays coming from a system with mean budget $\sum_ip_i\le B$; $P=P^{(2)}_{N,d}$ and $P_B=P^{(2;B)}_{N,d}$. For a set $A$ of pair arrays and a cap $u\ge0$, the **capped value** is
--   $$V_A(u)=\max\{1^{\mathsf T}q:\ q\in A,\ 0\le q\le u\}.$$
--   A **common LP** is a linear system with $s$ inequalities (equations and auxiliary variables free, real coefficients) projecting onto an output polyhedron $K$; it is fixed before the cap, each query adds the cap $0\le q\le u$ directly on the output, and its error at $u$ is $|V_K(u)-V_{\text{target}}(u)|$ (Section 1.3).
--
--   There is an absolute $\kappa>0$ such that, for each fixed $\theta\in(0,1)$, there are $\epsilon_\theta,c_\theta>0$ and $N_\theta$ with the following property. Let $N\ge N_\theta$, $d=\lfloor\theta N\rfloor$, let $a\ge2$ be an integer, and let $K\subseteq[0,1]^M$ have an $s$-inequality extended formulation whose capped feasible sets $\{q\in K:0\le q\le u\}$ are nonempty for all $u\in[0,1]^M$.
--
--   1. If $|V_K(u)-V_{P^{(a)}_{N,d}}(u)|\le\epsilon_\theta$ for every $u\in[0,1]^M$, then
--   $$s\ge2^{c_\theta N^\kappa}.$$
--   2. For any $B>2$, the same conclusion holds if $|V_K(u)-V_{P^{(a;B)}_{N,d}}(u)|\le\epsilon_\theta\min\{B-2,1\}$ for every $u\in[0,1]^M$.
--
--   The constants $\epsilon_\theta,c_\theta,N_\theta$ are uniform in $B$ and in the activity $a$.
--
--   No small common LP answers all capacity queries on the pair bodies to constant accuracy (or to accuracy proportional to the budget surplus), even though such an LP never has to describe the body exactly.
--
--   **Formalization Note** The constants are quantified in the printed order: $\kappa$ first, then $\epsilon_\theta,c_\theta,N_\theta$ after $\theta$, all before $N$, $a$, $B$ and the LP.
--
--   Differences from the source:
--   - encoding: the vertex set $[N]$ → `Fin N`; reason: the same set, indexed from zero
--   - encoding: a common LP (base formulation) with $s$ inequalities and output polyhedron $K$ → `IsEFOfSize K s` (platform); reason: the paper's counting convention (p.4, App. A.1): inequalities counted, equations and auxiliary variables free, real coefficients, unbounded lifts allowed
--   - encoding: $V_A(u)=\max\{1^{\mathsf T}q: q\in A,\ 0\le q\le u\}$ → `capValue A u`, the supremum of $\sum_e q_e$ over the capped set; reason: the capped set is nonempty and lies in the box $[0,u]$, and $A$ is a polyhedron or a compact body, so the supremum is attained and equals the maximum
--   - encoding: the constants and $N_\theta$ are uniform in $B$; both conclusions extend to every integer activity $a\ge2$, uniformly in $a$ → $\epsilon_\theta,c_\theta,N_\theta$ quantified before $\forall a\ge2$ and $\forall B>2$; the activity-two case is $a=2$; reason: this is the stated uniformity
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Theorem 1.2, p.5

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_MeanBudgetXC_pairBody
import Definitions.Def_MeanBudgetXC_budgetBody
import Definitions.Def_LinfContractionFP_unitCube
import Definitions.Def_MeanBudgetXC_Supplement_capValue

namespace MeanBudgetXC.Supplement

open ExtensionComplexity.TSP

/-- **Theorem 1.2** (Capacity lower bound for arbitrary common LPs) (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Theorem 1.2, p.5). There is an absolute `κ > 0` such that, for each fixed `θ ∈ (0, 1)`,
there are `ϵ_θ, c_θ > 0` and `N_θ` with the following property. Let `N ≥ N_θ`, `d = ⌊θN⌋`, and
let `K ⊆ [0, 1]^M` have an `s`-inequality extended formulation with nonempty capped feasible sets
for all `u ∈ [0, 1]^M`.
1. If `|V_K(u) − V_P(u)| ≤ ϵ_θ` for every such `u`, then `s ≥ 2^{c_θ N^κ}`.
2. For any `B > 2`, the same conclusion holds if `|V_K(u) − V_{P_B}(u)| ≤ ϵ_θ min{B − 2, 1}` for
   every `u ∈ [0, 1]^M`.
The constants and `N_θ` are uniform in `B`. Both conclusions extend to every integer activity
`a ≥ 2`, uniformly in `a`.

**Formalization Note** The vertex set is `Fin N`, `P^{(a)} = pairBody (Fin N) d a` and
`P^{(a;B)} = budgetBody (Fin N) d a B` (activity two is `a = 2`). "`K` has an `s`-inequality
extended formulation" is the platform's `IsEFOfSize K s` (inequalities counted, equations and
auxiliary variables free, real coefficients). `κ` is chosen first; `ϵ_θ, c_θ, N_θ` after `θ` and
before `N`, `a`, `B` and the LP. Finiteness of the capped values is automatic (the capped set
lies in the box `[0, u]`), so only nonemptiness is assumed. -/
theorem theorem_1_2 :
    ∃ κ : ℝ, 0 < κ ∧ ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∃ ϵ c : ℝ, 0 < ϵ ∧ 0 < c ∧ ∃ Nθ : ℕ, ∀ N ≥ Nθ, ∀ a : ℕ, 2 ≤ a →
        ∀ (K : Set (Pair (Fin N) → ℝ)) (s : ℕ), IsEFOfSize K s →
          K ⊆ LinfContractionFP.unitCube (Pair (Fin N)) →
          (∀ u ∈ LinfContractionFP.unitCube (Pair (Fin N)), (cappedSet K u).Nonempty) →
          ((∀ u ∈ LinfContractionFP.unitCube (Pair (Fin N)),
              |capValue K u - capValue (pairBody (Fin N) ⌊θ * N⌋₊ a) u| ≤ ϵ) →
            (2 : ℝ) ^ (c * (N : ℝ) ^ κ) ≤ s) ∧
          ∀ B : ℝ, 2 < B →
            (∀ u ∈ LinfContractionFP.unitCube (Pair (Fin N)),
              |capValue K u - capValue (budgetBody (Fin N) ⌊θ * N⌋₊ a B) u| ≤ ϵ * min (B - 2) 1) →
            (2 : ℝ) ^ (c * (N : ℝ) ^ κ) ≤ s := by sorry

end MeanBudgetXC.Supplement
