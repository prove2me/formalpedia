-- Prove2me | Theorems.Thm_MDPFinance_StructuredModels_convex_structure_theorem
-- name    : MDPFinance.StructuredModels.convex_structure_theorem
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:38:41.653631+00:00
-- url     : https://prove2.me/theorems/012ec783-3ab7-4283-a9bf-c7a36563596a
-- title:
--   Theorem 2.4.22 — the convex structure theorem (goal)
-- statement:
--   Suppose a Markov Decision Model $M$ with upper bounding function $b$ satisfies, for every
--   stage $n = 0,\dots,N-1$: (i) $E$ is convex and $D_n = E \times A$; (ii) for every convex $v \in
--   \mathbb{I\!B}_b^+$, $x \mapsto \int v(x')\,Q_n(dx' \mid x,a)$ is convex for every $a \in A$;
--   (iii) $x \mapsto r_n(x,a)$ is convex for every $a$; (iv) $g_N$ is convex; (v) every convex $v
--   \in \mathbb{I\!B}_b^+$ has a maximizer in $\Delta_n$. Then
--
--   $$
--   \mathrm{I\!M}_n := \{v \in \mathbb{I\!B}_b^+ : v \text{ convex}\}, \qquad (\Delta_n)_{n<N}
--   $$
--
--   satisfy the Structure Assumption (SAN).
--
--   **Formalization Note.** $E$, $A$ are general real vector spaces (not specialized to
--   $\mathbb{R}$), so hypothesis (i) ("$E$ convex") is a genuine, non-vacuous constraint; $D_n =
--   E \times A$ is stated as `M.D n = Set.univ`. Convexity of $v$ and of the integral term uses
--   `ConvexOnEReal`; convexity of $r_n$, $g_N$ (real-valued) uses Mathlib's own `ConvexOn`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 38, Theorem 2.4.22

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_StructureAssumption
import Definitions.Def_MDPFinance_StructuredModels_ConvexAnalysis

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

/-- Theorem 2.4.22 (Bäuerle–Rieder, p. 38, PDF 53) — the goal of this mission. Suppose a Markov
Decision Model with upper bounding function `b` is given and for all `n = 0, …, N-1` it holds:
(i) `E` is convex and `D_n := E × A`; (ii) for all convex `v ∈ IB_b^+`, `x ↦ ∫ v(x') Q_n(dx'|x,a)`
is convex for all `a ∈ A`; (iii) `x ↦ r_n(x,a)` is convex for all `a ∈ A`; (iv) `g_N` is convex;
(v) for all convex `v ∈ IB_b^+` there exists a maximizer `f_n ∈ Δ_n` of `v`. Then the sets
`IM_n := {v ∈ IB_b^+ | v convex}` and `Δ_n` satisfy the Structure Assumption (SAN). -/
theorem convex_structure_theorem {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup A] [Module ℝ A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (Deltas : ℕ → Set (E → A))
    (hEconvex : Convex ℝ (Set.univ : Set E))
    (hDn : ∀ n < N, M.D n = Set.univ)
    (hQ_convex : ∀ n < N, ∀ v ∈ IBbPlus b, ConvexOnEReal Set.univ v →
      ∀ a : A, ConvexOnEReal Set.univ (fun x => erealIntegral (M.Q n (x, a)) v))
    (hr_convex : ∀ n < N, ∀ a : A, ConvexOn ℝ Set.univ (fun x => M.r n (x, a)))
    (hg_convex : ConvexOn ℝ Set.univ M.g)
    (hmax : ∀ n < N, ∀ v ∈ IBbPlus b, ConvexOnEReal Set.univ v →
      ∃ f ∈ Deltas n, IsMaximizer M n v f) :
    StructureAssumption M (fun n => {v ∈ IBbPlus b | ConvexOnEReal Set.univ v}) Deltas := by sorry

end MDPFinance.StructuredModels
