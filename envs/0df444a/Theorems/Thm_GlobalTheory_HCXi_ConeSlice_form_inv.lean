-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeSlice_form_inv
-- name    : GlobalTheory.HCXi.ConeSlice.form_inv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:30:31.656378+00:00
-- url     : https://prove2.me/theorems/77ac0da7-bbb8-4ae8-919e-98bcbb83bc15
-- title:
--   Cone Slice: form inv
-- statement:
--   The Cone Slice construction uses the form inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L28-L36

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

theorem GlobalTheory.HCXi.ConeSlice.form_inv {k : ℕ} {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hg : gᴴ * sgnMat k * g = sgnMat k) (v : Fin (k + 1) → ℂ) :
    Complex.normSq ((g *ᵥ v) (Fin.last k)) - sqLen (Fin.init (g *ᵥ v) : Fin k → ℂ) =
      Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ) := by sorry
