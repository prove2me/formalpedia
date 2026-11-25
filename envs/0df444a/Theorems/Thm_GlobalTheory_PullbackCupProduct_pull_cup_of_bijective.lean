-- Prove2me | Theorems.Thm_GlobalTheory_PullbackCupProduct_pull_cup_of_bijective
-- name    : GlobalTheory.PullbackCupProduct.pull_cup_of_bijective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:57:52.687837+00:00
-- url     : https://prove2.me/theorems/3dd28772-fafe-4f50-906d-4ba990b22c3c
-- title:
--   Pullback Cup Product: pull cup of bijective
-- statement:
--   The Pullback Cup Product construction uses the pull cup of bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PullCupOfBijective.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PullCupOfBijective.lean#L18-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullCupOfBijective
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_cup

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
open GlobalTheory GlobalTheory.PullbackCupProduct
open GlobalTheory.CatCoh
universe u v u' v' u'' v''

theorem GlobalTheory.PullbackCupProduct.pull_cup_of_bijective {R R' : Type} [CommRing R] [CommRing R']
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
    {σ : R →+* R'} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
    {F'' : C'' ⥤ CommAlgCat.{0} R'} (m : CoefMap σ F F'') (n : CoefMap (RingHom.id R') F' F'')
    (h1 : Function.Bijective n.pull1) (h2 : Function.Bijective n.pull2) (a b : H1 F) :
    (LinearEquiv.ofBijective n.pull2 h2).symm (m.pull2 (cup F a b)) =
      cup F' ((LinearEquiv.ofBijective n.pull1 h1).symm (m.pull1 a))
        ((LinearEquiv.ofBijective n.pull1 h1).symm (m.pull1 b)) := by sorry
