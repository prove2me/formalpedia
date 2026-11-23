-- Prove2me | Theorems.Thm_GlobalTheory_SS_existsUnique_extension_of_forall_defAt
-- name    : GlobalTheory.SS.existsUnique_extension_of_forall_defAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:52:59.142809+00:00
-- url     : https://prove2.me/theorems/7c376a1c-ecbb-4735-9f6d-a5111b23d9cb
-- title:
--   SS: exists Unique extension of forall def At
-- statement:
--   The SS construction uses the exists Unique extension of forall def At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelExtensionOfDefinedAtPoints.lean#L149-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelExtensionOfDefinedAtPoints.lean#L149-L203

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPoints
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
open GlobalTheory GlobalTheory.SS
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)}

theorem GlobalTheory.SS.existsUnique_extension_of_forall_defAt :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
      [IsFractionRing R K] (A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (M : _root_.GlobalTheory.SS.Model R A)
      (N : _root_.GlobalTheory.SS.Model R A') (f : A ⟶ A'),
      (∀ y, _root_.GlobalTheory.SS.DefAt M N f y) →
        ∃! g : M.Y ⟶ N.Y,
          M.j ≫ g.left = f.left ≫ N.j := by sorry
