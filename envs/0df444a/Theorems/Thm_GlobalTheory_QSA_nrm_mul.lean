-- Prove2me | Theorems.Thm_GlobalTheory_QSA_nrm_mul
-- name    : GlobalTheory.QSA.nrm_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:32.499649+00:00
-- url     : https://prove2.me/theorems/82e27440-2215-4a22-b6a9-85568a2acfd7
-- title:
--   QSA: nrm mul
-- statement:
--   The QSA construction uses the nrm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneMemH0WeightZero.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OneMemH0WeightZero.lean#L33-L36

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

theorem GlobalTheory.QSA.nrm_mul {R : Type*} [CommRing R] {a b : R} (x y : ℍ[R, a, b]) : nrm (x * y) = nrm x * nrm y := by sorry
