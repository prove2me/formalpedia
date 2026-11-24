-- Prove2me | Theorems.Thm_GlobalTheory_BiextSignTwist_not_both
-- name    : GlobalTheory.BiextSignTwist.not_both
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:01:22.504322+00:00
-- url     : https://prove2.me/theorems/4f3eb9d6-4b1e-402b-8859-5ae55769eb3a
-- title:
--   Biext Sign Twist: not both
-- statement:
--   The Biext Sign Twist construction uses the not both property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AbelianLawCounterexamples/MulGenNegRight.lean#L94-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AbelianLawCounterexamples/MulGenNegRight.lean#L94-L135

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

theorem GlobalTheory.BiextSignTwist.not_both (h2 : IsUnit (2 : Γ(S, ⊤))) [Nonempty S] (L : RigLB G) (c : CubicalStr G L)
    (ψ : ULift.{u} (Fin 3) → ((G3 G).left ⟶ (G2 G).left))
    (law : LB.Gen (LB.LinComb (abelian₂ G L.L) ψ lawε)) (h : LawIsCube G L c ψ law) :
    ¬ LawIsCube G L c ψ (negGen law) := by sorry
