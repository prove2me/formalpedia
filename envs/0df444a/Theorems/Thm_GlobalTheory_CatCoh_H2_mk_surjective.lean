-- Prove2me | Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
-- name    : GlobalTheory.CatCoh.H2.mk_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:33.736824+00:00
-- url     : https://prove2.me/theorems/4ff3da80-7c36-46dd-afde-3737d01e9faf
-- title:
--   H2: mk surjective
-- statement:
--   The H2 construction uses the mk surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CommAlgFunctorCoboundaryZeroMemCocyclesOne.lean#L124-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CommAlgFunctorCoboundaryZeroMemCocyclesOne.lean#L124-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory
open GlobalTheory GlobalTheory.CatCoh
universe v u v' u' v'' u''
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
variable (F)

theorem GlobalTheory.CatCoh.H2.mk_surjective : Function.Surjective (H2.mk F) := by sorry
