-- Prove2me | Theorems.Thm_GlobalTheory_HomPairDescent_exists_descend
-- name    : GlobalTheory.HomPairDescent.exists_descend
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:54:07.064842+00:00
-- url     : https://prove2.me/theorems/78fdec42-5aea-5a3c-89b1-9e72f32fa9e0
-- title:
--   Hom Pair Descent: exists descend
-- statement:
--   The Hom Pair Descent construction uses the exists descend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomPairDescendsToFinite.lean#L36-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomPairDescendsToFinite.lean#L36-L61

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

theorem GlobalTheory.HomPairDescent.exists_descend {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A B : Over (Sp K))
    [QuasiCompact A.hom] [QuasiSeparated A.hom] [LocallyOfFinitePresentation B.hom]
    (f : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj B) :
    ∃ s : Finset Ω, ∀ L : IntermediateField K Ω, (s : Set Ω) ⊆ L →
      ∃ g : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ (Over.pullback (spMap (algebraMap K L))).obj B,
        bcMap A.hom L.val ≫ g.left = f.left ≫ bcMap B.hom L.val := by sorry
