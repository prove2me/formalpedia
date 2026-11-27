-- Prove2me | Theorems.Thm_GlobalTheory_T_proper_lift_trait_of_generic_lift
-- name    : GlobalTheory.T.proper_lift_trait_of_generic_lift
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:53.400553+00:00
-- url     : https://prove2.me/theorems/df1fee25-4bb9-5f40-855f-4ec731bb7308
-- title:
--   T: proper lift trait of generic lift
-- statement:
--   The T construction uses the proper lift trait of generic lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProperLiftTraitOfGenericLiftStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProperLiftTraitOfGenericLiftStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProperLiftTraitOfGenericLift
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProperLiftTraitOfGenericLiftStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.proper_lift_trait_of_generic_lift : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), IsProper π → ∀ (V V' : Type) [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (f : V →+* V') (fK : FractionRing V →+* FractionRing V'), (∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) → ∀ (ξ : Sp V ⟶ X) (y : Sp (FractionRing V') ⟶ Y), y ≫ π = spMap fK ≫ jK V ≫ ξ → ∃ ξ' : Sp V' ⟶ Y, ξ' ≫ π = spMap f ≫ ξ ∧ jK V' ≫ ξ' = y := by sorry
