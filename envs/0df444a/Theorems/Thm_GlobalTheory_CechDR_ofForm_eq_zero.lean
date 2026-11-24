-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_ofForm_eq_zero
-- name    : GlobalTheory.CechDR.ofForm_eq_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:36:23.68071+00:00
-- url     : https://prove2.me/theorems/519ae192-0a39-4c0d-acc1-53baf64dcdf9
-- title:
--   Cech DR: of Form eq zero
-- statement:
--   The Cech DR construction uses the of Form eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamTotalDifferentialOneFunctionPart.lean#L494-L515
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamTotalDifferentialOneFunctionPart.lean#L494-L515

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
variable {F}

theorem GlobalTheory.CechDR.ofForm_eq_zero {ω : Closed1 F} : ofForm F ω = 0 ↔
    ∃ g : C0 F, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), g T' = mp F φ (g T)) ∧ ∀ T, D R _ (g T) = ω.1.1 T := by sorry
