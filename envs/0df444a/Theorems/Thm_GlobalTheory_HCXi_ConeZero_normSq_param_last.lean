-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeZero_normSq_param_last
-- name    : GlobalTheory.HCXi.ConeZero.normSq_param_last
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:29:33.375203+00:00
-- url     : https://prove2.me/theorems/071c0915-7853-5612-9e53-d9815bb37ad0
-- title:
--   Cone Zero: norm Sq param last
-- statement:
--   The Cone Zero construction uses the norm Sq param last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasure.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasure.lean#L34-L39

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

theorem GlobalTheory.HCXi.ConeZero.normSq_param_last (n : ℕ) (p : (Fin n → ℂ) × ℝ) :
    Complex.normSq (param n p (Fin.last n)) = sqLen p.1 := by sorry
