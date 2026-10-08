-- Prove2me | Theorems.Thm_GabayMercier_Approximation_eq_4_8
-- name    : GabayMercier.Approximation.eq_4_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:32.663172+00:00
-- url     : https://prove2.me/theorems/5d3c0047-5941-4c6a-a546-70b0b79930e4
-- title:
--   Equation (4.8) — corrected continuous-space estimate
-- statement:
--   Under the continuous coercivity bound (2.5), for any $w\in V_k$ and $x\in V$,
--   $$
--   \alpha\|w-x\|\le\|A(w-x)\|\le\|Aw-A_kw\|+\|A_kw-Ax\|.
--   $$
--   This relates convergence of the discrete images to strong convergence in $V$.
--
--   **Formalization Note** The paper prints $A(v_h^*)$ in the middle and attributes the first bound to (4.1)(i). The intended middle term is $A(v_h^*-v^*)$, and the first bound follows from (2.5), because $v_h^*-v^*$ need not lie in $V_h$.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 22, (4.8)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_Approximation_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.Approximation

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- (4.8), corrected to use (2.5) on `w - x`. -/
theorem eq_4_8 (A : V →L[ℝ] Y) (f₂ : Y → EReal) (α : ℝ)
    (Vh : ℕ → Submodule ℝ V) (Ah : (k : ℕ) → Vh k →L[ℝ] Y)
    (α' M : ℝ) (h : ApproxHyp A f₂ α Vh Ah α' M)
    (k : ℕ) (w : Vh k) (x : V) :
    α * ‖(w : V) - x‖ ≤ ‖A ((w : V) - x)‖ ∧
    ‖A ((w : V) - x)‖ ≤ ‖A w - Ah k w‖ + ‖Ah k w - A x‖ := by sorry

end GabayMercier.Approximation
