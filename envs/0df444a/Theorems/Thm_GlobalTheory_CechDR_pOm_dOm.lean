-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_pOm_dOm
-- name    : GlobalTheory.CechDR.pOm_dOm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:49.347838+00:00
-- url     : https://prove2.me/theorems/ec3bb090-6e8f-4ba3-9770-a145d78cfb0f
-- title:
--   Cech DR: p Om d Om
-- statement:
--   The Cech DR construction uses the p Om d Om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamTotalDifferentialOneFunctionPart.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamTotalDifferentialOneFunctionPart.lean#L63-L66

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
variable {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'')

theorem GlobalTheory.CechDR.pOm_dOm {j : ℕ} (x : Om R (F.obj T) j) :
    pOm F (j + 1) φ (dOm R _ j x) = dOm R _ j (pOm F j φ x) := by sorry
