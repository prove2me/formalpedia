-- Prove2me | Theorems.Thm_GlobalTheory_SS_StrictLaw_ext_pt
-- name    : GlobalTheory.SS.StrictLaw.ext_pt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:30.516906+00:00
-- url     : https://prove2.me/theorems/5f850324-8edc-4045-9ec1-1ffab589a7b1
-- title:
--   Strict Law: ext pt
-- statement:
--   The Strict Law construction uses the ext pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsStrictModelOfBirational.lean#L194-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsStrictModelOfBirational.lean#L194-L224

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeronStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOnPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStrictModelOfBirational
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StrictLaw
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}

theorem GlobalTheory.SS.StrictLaw.ext_pt [IsDomain R] [IsFractionRing R K] {B B' : Over (Sp K)} {M : Model R A}
    {N : Model R B} {N' : Model R B'} {Q : Model R A'} {f : A ⟶ B} {f' : A ⟶ B'}
    {U U' : M.Y.left.Opens} {g : U.toScheme ⟶ N.Y.left} {g' : U'.toScheme ⟶ N'.Y.left}
    (h : Extends M N f U g) (h' : Extends M N' f' U' g') (p : N.Y ⟶ Q.Y) (p' : N'.Y ⟶ Q.Y)
    (e : f.left ≫ N.j ≫ p.left = f'.left ≫ N'.j ≫ p'.left)
    (u : U.toScheme) (u' : U'.toScheme) (hu : U.ι u = U'.ι u') :
    p.left (g u) = p'.left (g' u') := by sorry
