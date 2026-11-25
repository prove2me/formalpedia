-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_complete_dvr_integral_closure_finite
-- name    : GlobalTheory.T.exists_complete_dvr_integral_closure_finite
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:30:00.614121+00:00
-- url     : https://prove2.me/theorems/7fa9e0c6-185d-4bed-b1d5-7d3d749c9206
-- title:
--   T: exists complete dvr integral closure finite
-- statement:
--   The T construction uses the exists complete dvr integral closure finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCompleteDvrIntegralClosureFiniteStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCompleteDvrIntegralClosureFiniteStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDvrIntegralClosureFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDvrIntegralClosureFiniteStatement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_complete_dvr_integral_closure_finite : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L], ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : Algebra V W) (_ : Algebra W L) (_ : IsFractionRing W L), (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ Module.Finite V W ∧ Function.Injective (algebraMap V W) ∧ IsLocalHom (algebraMap V W) ∧ (∀ x : L, RingHom.IsIntegralElem ((algebraMap K L).comp (algebraMap V K)) x → x ∈ Set.range (algebraMap W L)) ∧ ∀ (A : Over (Sp K)) [GrpObj A] Q, PotModel W L ((Over.pullback (spMap (algebraMap K L))).obj A) Q → PotModel V K A Q := by sorry
