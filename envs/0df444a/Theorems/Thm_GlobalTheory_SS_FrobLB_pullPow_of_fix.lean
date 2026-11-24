-- Prove2me | Theorems.Thm_GlobalTheory_SS_FrobLB_pullPow_of_fix
-- name    : GlobalTheory.SS.FrobLB.pullPow_of_fix
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:34:09.078859+00:00
-- url     : https://prove2.me/theorems/023adc85-297a-48f7-9a01-7ba0ce0f36e6
-- title:
--   Frob LB: pull Pow of fix
-- statement:
--   The Frob LB construction uses the pull Pow of fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PullPowOfFix.lean#L78-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PullPowOfFix.lean#L78-L91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PullPowOfFix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobLB
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw

theorem GlobalTheory.SS.FrobLB.pullPow_of_fix {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (φ : X ⟶ X) (n : ℕ)
    {A : Type} (V : A → X.Opens) (c : A → L.ι) (hc : ∀ y, ∃ a, y ∈ V a) (hV : ∀ a, V a ≤ L.U (c a))
    (h : ∀ a b, Fix φ (V a ⊓ V b) (res (inf_le_inf (hV a) (hV b)) (L.g (c a) (c b))).val n) :
    PullPow φ L n := by sorry
