-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeZero_herm_param
-- name    : GlobalTheory.HCXi.ConeZero.herm_param
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:34:51.956308+00:00
-- url     : https://prove2.me/theorems/0e739b22-51d6-539a-9f40-6570192c93d8
-- title:
--   Cone Zero: herm param
-- statement:
--   The Cone Zero construction uses the herm param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasure.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasure.lean#L46-L55

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

theorem GlobalTheory.HCXi.ConeZero.herm_param (n : ℕ) (p : (Fin n → ℂ) × ℝ) :
    herm (Matrix.diagonal (fun i : Fin (n + 1) => if i = Fin.last n then (-1 : ℂ) else 1))
      (param n p) (param n p) = 0 := by sorry
