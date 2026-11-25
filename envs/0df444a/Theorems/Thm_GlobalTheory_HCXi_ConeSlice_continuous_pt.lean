-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeSlice_continuous_pt
-- name    : GlobalTheory.HCXi.ConeSlice.continuous_pt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:55.937497+00:00
-- url     : https://prove2.me/theorems/37c77882-59a7-41a2-97e6-fe58e03af237
-- title:
--   Cone Slice: continuous pt
-- statement:
--   The Cone Slice construction uses the continuous pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L119-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibrationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiber
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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeSlice

theorem GlobalTheory.HCXi.ConeSlice.continuous_pt {k : ℕ} :
    Continuous (fun q : ℝ × ((Fin k → ℂ) × ℝ) => pt q.1 q.2) := by sorry
