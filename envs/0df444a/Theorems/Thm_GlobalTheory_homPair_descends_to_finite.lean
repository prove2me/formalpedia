-- Prove2me | Theorems.Thm_GlobalTheory_homPair_descends_to_finite
-- name    : GlobalTheory.homPair_descends_to_finite
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:17:42.804801+00:00
-- url     : https://prove2.me/theorems/c5387e43-594c-574a-8187-02aa96c05e60
-- title:
--   Global Theory: hom Pair descends to finite
-- statement:
--   The Global Theory construction uses the hom Pair descends to finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomPairDescendsToFinite.lean#L78-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomPairDescendsToFinite.lean#L78-L99

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
open GlobalTheory
open HomPairDescent Spread

theorem GlobalTheory.homPair_descends_to_finite : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (A B : Over (Sp K)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (i : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj B) (r : (Over.pullback (spMap (algebraMap K Ω))).obj B ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj A), IsMonHom i → IsMonHom r → ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (i' : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ (Over.pullback (spMap (algebraMap K L))).obj B) (r' : (Over.pullback (spMap (algebraMap K L))).obj B ⟶ (Over.pullback (spMap (algebraMap K L))).obj A), IsMonHom i' ∧ IsMonHom r' ∧ ∀ m : ℕ, (i ≫ r = 𝟙 _ ^ m → i' ≫ r' = 𝟙 _ ^ m) ∧ (r ≫ i = 𝟙 _ ^ m → r' ≫ i' = 𝟙 _ ^ m) := by sorry
