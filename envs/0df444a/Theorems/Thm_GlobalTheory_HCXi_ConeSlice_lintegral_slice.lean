-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeSlice_lintegral_slice
-- name    : GlobalTheory.HCXi.ConeSlice.lintegral_slice
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:32:31.565717+00:00
-- url     : https://prove2.me/theorems/73904029-6873-499d-ad3c-84dbc211f775
-- title:
--   Cone Slice: lintegral slice
-- statement:
--   The Cone Slice construction uses the lintegral slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L157-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L157-L183

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

theorem GlobalTheory.HCXi.ConeSlice.lintegral_slice {k : ℕ} {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hg : gᴴ * sgnMat k * g = sgnMat k) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ τ in Set.Ioi 0, F τ * slice g τ = ∫⁻ τ in Set.Ioi 0, F τ * slice (k := k) 1 τ := by sorry
