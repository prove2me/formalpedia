-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_pOm_dTwo
-- name    : GlobalTheory.CechDR.pOm_dTwo
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:37:02.716315+00:00
-- url     : https://prove2.me/theorems/64977551-7eb9-4bbe-96a8-4fec848a59be
-- title:
--   Cech DR: p Om d Two
-- statement:
--   The Cech DR construction uses the p Om d Two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamTotalDifferentialOneFunctionPart.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CechDeRhamTotalDifferentialOneFunctionPart.lean#L72-L74

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

theorem GlobalTheory.CechDR.pOm_dTwo (x : Om R (F.obj T) 2) : pOm F 3 φ (dTwo R _ x) = dTwo R _ (pOm F 2 φ x) := by sorry
