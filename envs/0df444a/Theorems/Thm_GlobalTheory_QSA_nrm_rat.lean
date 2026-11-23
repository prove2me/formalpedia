-- Prove2me | Theorems.Thm_GlobalTheory_QSA_nrm_rat
-- name    : GlobalTheory.QSA.nrm_rat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:57.188724+00:00
-- url     : https://prove2.me/theorems/0d6f7cae-d5c2-43b0-bca0-fd58b8660f72
-- title:
--   QSA: nrm rat
-- statement:
--   The QSA construction uses the nrm rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneMemH0WeightZero.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneMemH0WeightZero.lean#L41-L42

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

theorem GlobalTheory.QSA.nrm_rat {a b : F} (x : ℍ[F, a, b]) : nrm (rat x) = algebraMap F (AF F) (nrm x) := by sorry
