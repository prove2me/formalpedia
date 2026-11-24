-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_toO_mk
-- name    : GlobalTheory.CechDR.toO_mk
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:35:34.532766+00:00
-- url     : https://prove2.me/theorems/1c97d5fc-355e-4aa9-b898-2313fefc4af6
-- title:
--   Cech DR: to O mk
-- statement:
--   The Cech DR construction uses the to O mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamTotalDifferentialOneFunctionPart.lean#L433-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamTotalDifferentialOneFunctionPart.lean#L433-L433

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
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
variable {F}
variable (F)

theorem GlobalTheory.CechDR.toO_mk (c : cechDeRhamTotalCocyclesOne F) : toO F (Hyp1.mk F c) = H1.mk F (cechDeRhamTotalCocyclesOne.fn F c) := by sorry
