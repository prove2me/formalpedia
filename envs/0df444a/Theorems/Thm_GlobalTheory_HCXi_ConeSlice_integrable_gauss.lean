-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeSlice_integrable_gauss
-- name    : GlobalTheory.HCXi.ConeSlice.integrable_gauss
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:31:54.213363+00:00
-- url     : https://prove2.me/theorems/7825d0c4-1e7c-40ae-93e1-3521dbac3e3d
-- title:
--   Cone Slice: integrable gauss
-- statement:
--   The Cone Slice construction uses the integrable gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L105-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L105-L117

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

theorem GlobalTheory.HCXi.ConeSlice.integrable_gauss {k : ℕ} {c : ℝ} (hc : 0 < c) :
    Integrable (fun w : Fin k → ℂ => Real.exp (-(c * sqLen w))) := by sorry
