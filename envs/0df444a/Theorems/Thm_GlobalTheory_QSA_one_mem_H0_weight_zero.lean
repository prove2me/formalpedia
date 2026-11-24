-- Prove2me | Theorems.Thm_GlobalTheory_QSA_one_mem_H0_weight_zero
-- name    : GlobalTheory.QSA.one_mem_H0_weight_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:03:17.711045+00:00
-- url     : https://prove2.me/theorems/7f356ba1-91be-4b10-8af3-52dc307c881e
-- title:
--   QSA: one mem H0 weight zero
-- statement:
--   The QSA construction uses the one mem H0 weight zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneMemH0WeightZero.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneMemH0WeightZero.lean#L44-L45

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneMemH0WeightZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Quaternion
open GlobalTheory GlobalTheory.QSA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable (F : Type) [Field F] [NumberField F]
variable {F}

theorem GlobalTheory.QSA.one_mem_H0_weight_zero {a b : F} (ε : AF F) : (1 : DA F a b) ∈ H0 ε := by sorry
