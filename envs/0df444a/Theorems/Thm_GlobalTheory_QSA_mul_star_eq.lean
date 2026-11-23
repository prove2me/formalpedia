-- Prove2me | Theorems.Thm_GlobalTheory_QSA_mul_star_eq
-- name    : GlobalTheory.QSA.mul_star_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:50.427483+00:00
-- url     : https://prove2.me/theorems/f676933a-320e-41c7-95c3-eed0233dbf1d
-- title:
--   QSA: mul star eq
-- statement:
--   The QSA construction uses the mul star eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneMemH0WeightZero.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneMemH0WeightZero.lean#L38-L39

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

theorem GlobalTheory.QSA.mul_star_eq {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) : x * star x = algebraMap R ℍ[R, a, b] (nrm x) := by sorry
