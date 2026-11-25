-- Prove2me | Theorems.Thm_GlobalTheory_BiextSignTwist_main
-- name    : GlobalTheory.BiextSignTwist.main
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:48.129007+00:00
-- url     : https://prove2.me/theorems/c505b650-3cb8-562e-8f5b-1b5690d1e8e2
-- title:
--   Biext Sign Twist: main
-- statement:
--   The Biext Sign Twist construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AbelianLawCounterexamples/MulGenNegRight.lean#L195-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AbelianLawCounterexamples/MulGenNegRight.lean#L195-L200

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_TrivialBiextension
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_MulGenNegRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
universe u
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BiextSignTwist
variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsCommMonObj G]
open GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension (trivLB pull_one mul_one' corr_one isGen_one)

theorem GlobalTheory.BiextSignTwist.main (h2 : IsUnit (2 : Γ(S, ⊤))) [Nonempty S] :
    (LawIsCube G _ (oneCub G) _ (oneBiext G).law1 ∧ LawIsCube G _ (oneCub G) _ (oneBiext G).law2) ∧
    ¬ LawIsCube G _ (oneCub G) _ (negBiext G (oneBiext G)).law1 := by sorry
