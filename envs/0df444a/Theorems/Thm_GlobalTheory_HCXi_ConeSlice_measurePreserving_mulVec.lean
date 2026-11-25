-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeSlice_measurePreserving_mulVec
-- name    : GlobalTheory.HCXi.ConeSlice.measurePreserving_mulVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:32:30.959801+00:00
-- url     : https://prove2.me/theorems/ccc66d52-77c7-4fdb-a3be-ff12be35c441
-- title:
--   Cone Slice: measure Preserving mul Vec
-- statement:
--   The Cone Slice construction uses the measure Preserving mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L58-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L58-L68

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

theorem GlobalTheory.HCXi.ConeSlice.measurePreserving_mulVec {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Complex.normSq g.det = 1) :
    MeasurePreserving (fun v : Fin n → ℂ => g *ᵥ v) volume volume := by sorry
