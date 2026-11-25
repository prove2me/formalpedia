-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeSlice_exists_lower
-- name    : GlobalTheory.HCXi.ConeSlice.exists_lower
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:40.323588+00:00
-- url     : https://prove2.me/theorems/d5fb880c-8562-4a3b-9f30-ad85e0ab23ef
-- title:
--   Cone Slice: exists lower
-- statement:
--   The Cone Slice construction uses the exists lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L70-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean#L70-L103

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

theorem GlobalTheory.HCXi.ConeSlice.exists_lower {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g.det ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, c * sqLen v ≤ sqLen (g *ᵥ v) := by sorry
