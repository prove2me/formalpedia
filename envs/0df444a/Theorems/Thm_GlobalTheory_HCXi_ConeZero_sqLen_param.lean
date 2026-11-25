-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeZero_sqLen_param
-- name    : GlobalTheory.HCXi.ConeZero.sqLen_param
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:11:20.92711+00:00
-- url     : https://prove2.me/theorems/51df16ea-e012-4942-8372-05bb1a246590
-- title:
--   Cone Zero: sq Len param
-- statement:
--   The Cone Zero construction uses the sq Len param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasure.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasure.lean#L41-L44

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

theorem GlobalTheory.HCXi.ConeZero.sqLen_param (n : ℕ) (p : (Fin n → ℂ) × ℝ) : sqLen (param n p) = 2 * sqLen p.1 := by sorry
