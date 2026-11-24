-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CubeOpen_eq_bot_of_small
-- name    : GlobalTheory.AbLaw.CubeOpen.eq_bot_of_small
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:52:31.620839+00:00
-- url     : https://prove2.me/theorems/86a488c4-2d7d-4401-bd3e-d8781adc4259
-- title:
--   Cube Open: eq bot of small
-- statement:
--   The Cube Open construction uses the eq bot of small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivBasicOpenOfTrivFibre.lean#L42-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivBasicOpenOfTrivFibre.lean#L42-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeOpen

theorem GlobalTheory.AbLaw.CubeOpen.eq_bot_of_small {S : Type} [CommRing S] [IsLocalRing S] (J : Ideal S) (hJ : J.FG)
    (H : ∀ (I' : Ideal S) (e : S), e ∈ J → IsLocalRing.maximalIdeal S * J ≤ I' → I' ≤ J →
      J ≤ I' ⊔ Ideal.span {e} → J ≤ I') : J = ⊥ := by sorry
