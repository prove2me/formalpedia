-- Prove2me | Theorems.Thm_GlobalTheory_SS_essFiniteType_residueField_of_locallyOfFiniteType
-- name    : GlobalTheory.SS.essFiniteType_residueField_of_locallyOfFiniteType
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:38:07.702473+00:00
-- url     : https://prove2.me/theorems/ceae7414-c90a-40ee-be30-db28bab5bd97
-- title:
--   SS: ess Finite Type residue Field of locally Of Finite Type
-- statement:
--   The SS construction uses the ess Finite Type residue Field of locally Of Finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFieldOfValues.lean#L27-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFieldOfValues.lean#L27-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFieldOfValues
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

theorem GlobalTheory.SS.essFiniteType_residueField_of_locallyOfFiniteType {X : Scheme.{0}} {R : CommRingCat.{0}}
    (s : X ⟶ Spec R) [LocallyOfFiniteType s] (p : X) (ψ : R ⟶ X.residueField p)
    (h : Spec.map ψ = X.fromSpecResidueField p ≫ s) : ψ.hom.EssFiniteType := by sorry
