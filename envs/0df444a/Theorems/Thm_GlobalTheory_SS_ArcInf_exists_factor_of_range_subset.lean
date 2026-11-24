-- Prove2me | Theorems.Thm_GlobalTheory_SS_ArcInf_exists_factor_of_range_subset
-- name    : GlobalTheory.SS.ArcInf.exists_factor_of_range_subset
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:33:55.866801+00:00
-- url     : https://prove2.me/theorems/803c13f8-8463-43a4-b450-f1d86373c8d6
-- title:
--   Arc Inf: exists factor of range subset
-- statement:
--   The Arc Inf construction uses the exists factor of range subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFactorOfRangeSubset.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFactorOfRangeSubset.lean#L16-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFactorOfRangeSubset
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
open GlobalTheory.SS.ArcInf
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.ArcInf

theorem GlobalTheory.SS.ArcInf.exists_factor_of_range_subset {k : Type} [CommRing k] {G : Over (Sp k)} {A B : Type} [CommRing A]
    [Algebra k A] [CommRing B] [Algebra k B] (j : algOver k A ⟶ G) (hj : IsOpenImmersion j.left)
    (a : algOver k B ⟶ G) (hr : Set.range a.left ⊆ Set.range j.left) :
    ∃ χ : A →ₐ[k] B, algOverHom χ ≫ j = a := by sorry
