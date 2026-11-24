-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
-- name    : GlobalTheory.CechDR.Hyp2.mk_eq_mk
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:35:34.475618+00:00
-- url     : https://prove2.me/theorems/0388d508-3a46-4558-90c8-1f73673d2ad3
-- title:
--   Hyp2: mk eq mk
-- statement:
--   The Hyp2 construction uses the mk eq mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamTotalDifferentialOneFunctionPart.lean#L334-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamTotalDifferentialOneFunctionPart.lean#L334-L336

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk

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

theorem GlobalTheory.CechDR.Hyp2.mk_eq_mk {c c' : cechDeRhamTotalCocyclesTwo F} : Hyp2.mk F c = Hyp2.mk F c' ↔ ∃ e, dTot1 F e = c.1 - c'.1 := by sorry
