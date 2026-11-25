-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_constHom_comp_charHom
-- name    : GlobalTheory.PDivGroup.constHom_comp_charHom
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:09.695774+00:00
-- url     : https://prove2.me/theorems/e99254db-b2de-483c-a35d-c2048853ceb1
-- title:
--   PDiv Group: const Hom comp char Hom
-- statement:
--   The PDiv Group construction uses the const Hom comp char Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1102-L1104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1102-L1104

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
variable {B : Type} [CommRing B] [Algebra O B]

theorem GlobalTheory.PDivGroup.constHom_comp_charHom (t : G.Tate) (χ : G.dual.Tate) :
    constHom G t ≫ charHom G χ = constHom (mu p O) (pairing G O t χ) := by sorry
