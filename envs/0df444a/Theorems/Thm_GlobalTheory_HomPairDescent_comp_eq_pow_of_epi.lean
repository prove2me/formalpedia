-- Prove2me | Theorems.Thm_GlobalTheory_HomPairDescent_comp_eq_pow_of_epi
-- name    : GlobalTheory.HomPairDescent.comp_eq_pow_of_epi
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:46:32.906415+00:00
-- url     : https://prove2.me/theorems/fa66a49e-48f5-412d-a1fb-205b729fa888
-- title:
--   Hom Pair Descent: comp eq pow of epi
-- statement:
--   The Hom Pair Descent construction uses the comp eq pow of epi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomPairDescendsToFinite.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomPairDescendsToFinite.lean#L63-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsMonHomIffOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomPairDescendsToFinite
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
open GlobalTheory GlobalTheory.HomPairDescent
open GlobalTheory.Spread

theorem GlobalTheory.HomPairDescent.comp_eq_pow_of_epi {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} [GrpObj G] {G' H' : Over S'}
    [GrpObj G'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (h : IsGrpPullback G' G j φ) [Epi φ]
    {a' : G' ⟶ H'} {b' : H' ⟶ G'} {a : G ⟶ H} {b : H ⟶ G}
    (ha : φ ≫ a.left = a'.left ≫ ψ) (hb : ψ ≫ b.left = b'.left ≫ φ) (m : ℕ)
    (e : a' ≫ b' = 𝟙 _ ^ m) : a ≫ b = 𝟙 _ ^ m := by sorry
