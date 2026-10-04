-- Prove2me | Theorems.Thm_MDPFinance_StructuredModels_concave_structure_theorem
-- name    : MDPFinance.StructuredModels.concave_structure_theorem
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:38:30.969799+00:00
-- url     : https://prove2.me/theorems/59f8fb1b-6c71-4352-89bf-0bd73e414842
-- title:
--   Theorem 2.4.19 — the concave structure theorem
-- statement:
--   Suppose a Markov Decision Model $M$ with upper bounding function $b$ satisfies, for every $n$:
--   (i) $D_n$ convex in $E \times A$; (ii) $(x,a) \mapsto \int v(x')\,Q_n(dx' \mid x,a)$ concave
--   for every concave $v \in \mathbb{I\!B}_b^+$; (iii) $(x,a) \mapsto r_n(x,a)$ concave; (iv) $g_N$
--   concave; (v) every concave $v \in \mathbb{I\!B}_b^+$ has a maximizer in $\Delta_n$. Then
--
--   $$
--   \mathrm{I\!M}_n := \{v \in \mathbb{I\!B}_b^+ : v \text{ concave}\}, \qquad (\Delta_n)_{n<N}
--   $$
--
--   satisfy (SAN).
--
--   **Formalization Note.** $r_n$'s and $g_N$'s concavity uses Mathlib's own real-valued
--   `ConcaveOn` directly (no `EReal` needed, since $r_n$, $g_N$ are $\mathbb{R}$-valued); $v$'s
--   and the integral term's concavity use `ConcaveOnEReal`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 36, Theorem 2.4.19

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_StructureAssumption
import Definitions.Def_MDPFinance_StructuredModels_ConvexAnalysis

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

/-- Theorem 2.4.19 (Bäuerle–Rieder, p. 36, PDF 52). Suppose a Markov Decision Model with upper
bounding function `b` is given and for all `n = 0, …, N-1` it holds: (i) `D_n` is convex in
`E × A`; (ii) the mapping `(x,a) ↦ ∫ v(x') Q_n(dx'|x,a)` is concave for all concave `v ∈ IB_b^+`;
(iii) `(x,a) ↦ r_n(x,a)` is concave; (iv) `g_N` is concave on `E`; (v) for all concave
`v ∈ IB_b^+` there exists a maximizer `f_n ∈ Δ_n` of `v`. Then the sets
`IM_n := {v ∈ IB_b^+ | v concave}` and `Δ_n` satisfy the Structure Assumption (SAN). -/
theorem concave_structure_theorem {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup A] [Module ℝ A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (Deltas : ℕ → Set (E → A))
    (hD_convex : ∀ n < N, Convex ℝ (M.D n))
    (hQ_concave : ∀ n < N, ∀ v ∈ IBbPlus b, ConcaveOnEReal Set.univ v →
      ConcaveOnEReal (M.D n) (fun xa => erealIntegral (M.Q n xa) v))
    (hr_concave : ∀ n < N, ConcaveOn ℝ (M.D n) (M.r n))
    (hg_concave : ConcaveOn ℝ Set.univ M.g)
    (hmax : ∀ n < N, ∀ v ∈ IBbPlus b, ConcaveOnEReal Set.univ v →
      ∃ f ∈ Deltas n, IsMaximizer M n v f) :
    StructureAssumption M (fun n => {v ∈ IBbPlus b | ConcaveOnEReal Set.univ v}) Deltas := by sorry

end MDPFinance.StructuredModels
