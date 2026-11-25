-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeZero_Hpk_zero
-- name    : GlobalTheory.HCXi.ConeZero.Hpk_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:34:23.842191+00:00
-- url     : https://prove2.me/theorems/ea151ba8-9642-5dd5-9e67-26b7d402f4f7
-- title:
--   Cone Zero: Hpk zero
-- statement:
--   The Cone Zero construction uses the Hpk zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasure.lean#L138-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasure.lean#L138-L147

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

theorem GlobalTheory.HCXi.ConeZero.Hpk_zero (k : ℕ) : Hpk k 0 = Matrix.diagonal
    (fun i : Fin (2 * 0 + k + 1) => if i = Fin.last (2 * 0 + k) then (-1 : ℂ) else 1) := by sorry
