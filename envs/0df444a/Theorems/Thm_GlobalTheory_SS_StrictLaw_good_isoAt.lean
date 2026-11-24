-- Prove2me | Theorems.Thm_GlobalTheory_SS_StrictLaw_good_isoAt
-- name    : GlobalTheory.SS.StrictLaw.good_isoAt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:38:21.344982+00:00
-- url     : https://prove2.me/theorems/50c0ae98-4e44-4829-985b-0c3d814607ab
-- title:
--   Strict Law: good iso At
-- statement:
--   The Strict Law construction uses the good iso At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsStrictModelOfBirational.lean#L308-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsStrictModelOfBirational.lean#L308-L344

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

theorem GlobalTheory.SS.StrictLaw.good_isoAt {M N : Model R A} (i : N.Y ⟶ M.Y) [IsOpenImmersion i.left]
    (hj : N.j ≫ i.left = M.j) {f : A ⊗ A ⟶ A ⊗ A} {z : (M.prod M).Y.left}
    (h : Good M f (Set.range i.left) z) :
    ∃ w : (N.prod N).Y.left, i.left ((pr₁ N N).left w) = (pr₁ M M).left z ∧
      i.left ((pr₂ N N).left w) = (pr₂ M M).left z ∧
      IsoAt (N.prod N) (N.prod N) f w := by sorry
