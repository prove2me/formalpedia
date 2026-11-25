-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_charHom_tateMap
-- name    : GlobalTheory.PDivGroup.charHom_tateMap
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:27:11.937377+00:00
-- url     : https://prove2.me/theorems/5c518d88-9e8f-4b4e-a5e6-0911f7900e13
-- title:
--   PDiv Group: char Hom tate Map
-- statement:
--   The PDiv Group construction uses the char Hom tate Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L931-L934
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L931-L934

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory
open PDiv
open GlobalTheory.PDivGroup
attribute [instance] commRing hopf cocomm finite projective
variable {p : ℕ} {O : Type} [CommRing O]
variable {G H : PDivGroup p O}
variable [Fact p.Prime]

theorem GlobalTheory.PDivGroup.charHom_tateMap (f : G ⟶ H) (χ : H.dual.Tate) :
    charHom G (tateMap _ _ O (dualHom G H f) χ) = f ≫ charHom H χ := by sorry
