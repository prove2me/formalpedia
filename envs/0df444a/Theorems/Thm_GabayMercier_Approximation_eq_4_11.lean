-- Prove2me | Theorems.Thm_GabayMercier_Approximation_eq_4_11
-- name    : GabayMercier.Approximation.eq_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:36.558977+00:00
-- url     : https://prove2.me/theorems/ac7fcc9a-9295-40e9-ae6d-e4a69485e9be
-- title:
--   Equation (4.11) — vanishing image discrepancy
-- statement:
--   Under the hypotheses of Theorem 4.1, let $v^*$ solve $({\cal P})$ and let $v_k^*$ be any eventual discrete solutions. With $X_k=\|A_kv_k^*-Av^*\|^2$,
--   $$
--   X_k\longrightarrow0.
--   $$
--   This is (4.11), obtained in the paper by choosing $v=v^*$ in (4.10). Combined with (4.8) and (4.1)(iv), it yields strong convergence of the minimizers.
--
--   **Formalization Note** The limit is in the real norm topology and applies to every eventual selection of solutions.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 22, (4.11)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_Approximation_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.Approximation

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- (4.11): the discrepancy `Xₕ` vanishes. -/
theorem eq_4_11 (A : V →L[ℝ] Y) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (α : ℝ) (Vh : ℕ → Submodule ℝ V) [∀ k, FiniteDimensional ℝ (Vh k)]
    (Ah : (k : ℕ) → Vh k →L[ℝ] Y) (α' M : ℝ)
    (h : ApproxHyp A f₂ α Vh Ah α' M) (vs : V)
    (hvs : GabayMercier.DualAlgorithm.IsSolution A halfSq f₂ b vs)
    (vh : (k : ℕ) → Vh k) (hvh : ∀ᶠ k in atTop, IsSolutionH (Ah k) f₂ b (vh k)) :
    Tendsto (fun k => ‖Ah k (vh k) - A vs‖ ^ 2) atTop (𝓝 0) := by sorry

end GabayMercier.Approximation
