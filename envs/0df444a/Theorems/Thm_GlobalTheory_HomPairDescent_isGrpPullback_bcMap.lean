-- Prove2me | Theorems.Thm_GlobalTheory_HomPairDescent_isGrpPullback_bcMap
-- name    : GlobalTheory.HomPairDescent.isGrpPullback_bcMap
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:54:14.143988+00:00
-- url     : https://prove2.me/theorems/5adc9822-2a84-5cb5-baa3-e1f6c5a27799
-- title:
--   Hom Pair Descent: is Grp Pullback bc Map
-- statement:
--   The Hom Pair Descent construction uses the is Grp Pullback bc Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomPairDescendsToFinite.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomPairDescendsToFinite.lean#L29-L34

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

theorem GlobalTheory.HomPairDescent.isGrpPullback_bcMap {k R S : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (A : Over (Sp k)) [GrpObj A] (ρ : R →ₐ[k] S) :
    IsGrpPullback ((Over.pullback (spMap (algebraMap k S))).obj A) ((Over.pullback (spMap (algebraMap k R))).obj A)
      (spMap ρ.toRingHom) (bcMap A.hom ρ) := by sorry
