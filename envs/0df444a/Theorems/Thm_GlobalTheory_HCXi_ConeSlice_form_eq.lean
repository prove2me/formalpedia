-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeSlice_form_eq
-- name    : GlobalTheory.HCXi.ConeSlice.form_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:32.614867+00:00
-- url     : https://prove2.me/theorems/9d6a0283-1406-4b5e-97d1-891b5be9c848
-- title:
--   Cone Slice: form eq
-- statement:
--   The Cone Slice construction uses the form eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L19-L26

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

theorem GlobalTheory.HCXi.ConeSlice.form_eq {k : ℕ} (v : Fin (k + 1) → ℂ) :
    star v ⬝ᵥ (sgnMat k *ᵥ v) =
      ((sqLen (Fin.init v : Fin k → ℂ) - Complex.normSq (v (Fin.last k)) : ℝ) : ℂ) := by sorry
