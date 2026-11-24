-- Prove2me | Theorems.Thm_GlobalTheory_HodgeCurvPoint_dual_bound
-- name    : GlobalTheory.HodgeCurvPoint.dual_bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:49:12.291787+00:00
-- url     : https://prove2.me/theorems/5c80b0f3-29af-4b07-9fde-8ce6dea20be0
-- title:
--   Hodge Curv Point: dual bound
-- statement:
--   The Hodge Curv Point construction uses the dual bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeCurvatureDualMetricPointwiseBound.lean#L61-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeCurvatureDualMetricPointwiseBound.lean#L61-L184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeCurvPoint
variable {g : ℕ}

theorem GlobalTheory.HodgeCurvPoint.dual_bound : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ)
    (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K : ℝ), 0 < c → 0 ≤ K →
    Y.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, (Bs i).PosSemidef) → (∀ i, 0 < t i) →
    (∀ i x, t i * (x ⬝ᵥ Bs i *ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ j k, ‖Dm j k‖ ≤ K) →
    (Y.map Complex.ofReal).PosDef ∧ ∀ v, ‖form (Y.map Complex.ofReal)⁻¹
      ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v)
      ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v)‖ ≤
      (g * K / c + ∑ i, ‖s i‖ / t i) ^ 2 * gnorm (Y.map Complex.ofReal) v ^ 2 := by sorry
