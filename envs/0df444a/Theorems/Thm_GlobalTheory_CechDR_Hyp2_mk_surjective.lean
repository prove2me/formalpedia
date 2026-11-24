-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
-- name    : GlobalTheory.CechDR.Hyp2.mk_surjective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:35:05.776527+00:00
-- url     : https://prove2.me/theorems/8054f976-76e5-4083-8a07-fa1fd6096606
-- title:
--   Hyp2: mk surjective
-- statement:
--   The Hyp2 construction uses the mk surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamTotalDifferentialOneFunctionPart.lean#L308-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamTotalDifferentialOneFunctionPart.lean#L308-L308

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective

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
open CategoryTheory KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
open CatCoh
universe v u v' u' v'' u''
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
variable (F)

theorem GlobalTheory.CechDR.Hyp2.mk_surjective : Function.Surjective (Hyp2.mk F) := by sorry
