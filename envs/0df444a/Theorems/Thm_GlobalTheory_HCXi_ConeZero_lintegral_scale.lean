-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeZero_lintegral_scale
-- name    : GlobalTheory.HCXi.ConeZero.lintegral_scale
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:57.098886+00:00
-- url     : https://prove2.me/theorems/360e521a-25c2-49e2-af82-dce0fd4ced2c
-- title:
--   Cone Zero: lintegral scale
-- statement:
--   The Cone Zero construction uses the lintegral scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasure.lean#L71-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasure.lean#L71-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiberStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeZero

theorem GlobalTheory.HCXi.ConeZero.lintegral_scale (n : ℕ) (s : ℝ) (hs : 0 < s) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w : Fin n → ℂ, F (s * sqLen w)
      = ENNReal.ofReal (s ^ (-(n : ℝ))) * ∫⁻ w : Fin n → ℂ, F (sqLen w) := by sorry
