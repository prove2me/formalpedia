-- Prove2me | Theorems.Thm_GabayMercier_Approximation_solution_bounded
-- name    : GabayMercier.Approximation.solution_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:57.855838+00:00
-- url     : https://prove2.me/theorems/2c84e8f4-4cc9-403b-b589-b20954a2d802
-- title:
--   Uniform boundedness of the discrete solutions
-- statement:
--   Under the assumptions of Theorem 4.1, let $v^*$ solve $({\cal P})$. For every family $v_k^*\in V_k$ that solves $({\cal P}_k)$ for all sufficiently large $k$, there is a constant $C\in\mathbb R$ such that
--   $$
--   \|v_k^*\|\le C\qquad\text{for all sufficiently large }k.
--   $$
--   This is the boundedness conclusion immediately following (4.5); it permits weak subsequence arguments and use of (4.1)(iv).
--
--   **Formalization Note** Unlike the printed intermediate estimate, this conclusion does not require $f_2(0)<+\infty$: comparison with the (4.3) approximants of $v^*$ supplies a finite bound. The statement covers every eventual selection of discrete minimizers.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 21, after (4.5)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_Approximation_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.Approximation

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The conclusion `‖vₕ*‖ ≤ C` following (4.5). -/
theorem solution_bounded (A : V →L[ℝ] Y) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (α : ℝ) (Vh : ℕ → Submodule ℝ V) [∀ k, FiniteDimensional ℝ (Vh k)]
    (Ah : (k : ℕ) → Vh k →L[ℝ] Y) (α' M : ℝ)
    (h : ApproxHyp A f₂ α Vh Ah α' M) (vs : V)
    (hvs : GabayMercier.DualAlgorithm.IsSolution A halfSq f₂ b vs)
    (vh : (k : ℕ) → Vh k) (hvh : ∀ᶠ k in atTop, IsSolutionH (Ah k) f₂ b (vh k)) :
    ∃ C : ℝ, ∀ᶠ k in atTop, ‖(vh k : V)‖ ≤ C := by sorry

end GabayMercier.Approximation
