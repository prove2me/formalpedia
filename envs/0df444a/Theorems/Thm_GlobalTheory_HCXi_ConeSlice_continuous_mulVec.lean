-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeSlice_continuous_mulVec
-- name    : GlobalTheory.HCXi.ConeSlice.continuous_mulVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:40:19.692247+00:00
-- url     : https://prove2.me/theorems/3358bbdc-139a-4697-9476-ee7781dad2dd
-- title:
--   Cone Slice: continuous mul Vec
-- statement:
--   The Cone Slice construction uses the continuous mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L54-L56

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

theorem GlobalTheory.HCXi.ConeSlice.continuous_mulVec {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun v : Fin n → ℂ => g *ᵥ v) := by sorry
