-- Prove2me | Theorems.Thm_GlobalTheory_SS_Height_od_section
-- name    : GlobalTheory.SS.Height.od_section
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:17.545064+00:00
-- url     : https://prove2.me/theorems/44d881fd-9ae3-486f-9c27-62056fe7e6e4
-- title:
--   Height: od section
-- statement:
--   The Height construction uses the od section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleHeightProperScheme.lean#L139-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleHeightProperScheme.lean#L139-L156

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
variable (Pl : Places k K)

theorem GlobalTheory.SS.Height.od_section (i) {X : Scheme.{0}} (b : Sp (Pl.O i) ⟶ X) (x : Sp K ⟶ X)
    (hb : spMap (Pl.O i).subtype ≫ b = x) (U : X.Opens) (h : b (closedPoint (Pl.O i)) ∈ U) (f : Γ(X, U))
    (u : ((Sp K).presheaf.stalk (closedPoint K))ˣ) (hu : gs x (closedPoint K) U f = u.val) :
    0 ≤ od Pl i u ∧ (od Pl i u = 0 ↔ b (closedPoint (Pl.O i)) ∈ X.basicOpen f) := by sorry
