-- Prove2me | Theorems.Thm_GlobalTheory_T_henselian_iUnion_complete_of_integral_over_complete_dvr
-- name    : GlobalTheory.T.henselian_iUnion_complete_of_integral_over_complete_dvr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:33:35.820984+00:00
-- url     : https://prove2.me/theorems/19ab01ff-33a2-41db-a207-88e44a90edad
-- title:
--   T: henselian i Union complete of integral over complete dvr
-- statement:
--   The T construction uses the henselian i Union complete of integral over complete dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HenselianIUnionCompleteOfIntegralOverCompleteDvrStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HenselianIUnionCompleteOfIntegralOverCompleteDvrStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HenselianIUnionCompleteOfIntegralOverCompleteDvr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HenselianIUnionCompleteOfIntegralOverCompleteDvrStatement
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

theorem GlobalTheory.T.henselian_iUnion_complete_of_integral_over_complete_dvr : ∀ (W R : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [CharZero W] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra W R], Function.Injective (algebraMap W R) → Algebra.IsIntegral W R → IsLocalHom (algebraMap W R) ∧ HenselianLocalRing R ∧ ∀ s : Finset R, ∃ (W' : Subalgebra W R) (_ : IsDiscreteValuationRing W'), (↑s : Set R) ⊆ W' ∧ IsAdicComplete (IsLocalRing.maximalIdeal W') W' ∧ Module.Finite W W' ∧ IsLocalHom W'.val.toRingHom := by sorry
