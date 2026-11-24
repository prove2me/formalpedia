-- Prove2me | Theorems.Thm_GlobalTheory_SS_Height_centre_finite
-- name    : GlobalTheory.SS.Height.centre_finite
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:35:43.549527+00:00
-- url     : https://prove2.me/theorems/23079197-09e8-4f4d-a716-0b6695e7cd23
-- title:
--   Height: centre finite
-- statement:
--   The Height construction uses the centre finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleHeightProperScheme.lean#L71-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleHeightProperScheme.lean#L71-L111

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperScheme
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Height
open IsLocalRing
variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem GlobalTheory.SS.Height.centre_finite (Pl : Places k K) (B : Over (Sp k)) [IsProper B.hom]
    (x : Over.mk (spMap (algebraMap k K)) ⟶ B) (b : ∀ i, Sp (Pl.O i) ⟶ B.left)
    (hb : ∀ i, spMap (Pl.O i).subtype ≫ b i = x.left) (U : B.left.Opens) (hU : x.left (closedPoint K) ∈ U) :
    {i | b i (closedPoint (Pl.O i)) ∉ U}.Finite := by sorry
