-- Prove2me | Theorems.Thm_GlobalTheory_SS_DefectZero_mem_span_of_map_eq_zero
-- name    : GlobalTheory.SS.DefectZero.mem_span_of_map_eq_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:33:37.143111+00:00
-- url     : https://prove2.me/theorems/a5225aae-ae84-45c6-8fd3-b382ef87add6
-- title:
--   Defect Zero: mem span of map eq zero
-- statement:
--   The Defect Zero construction uses the mem span of map eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZero.lean#L154-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZero.lean#L154-L182

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZero
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
open TensorProduct KaehlerDifferential
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.DefectZero

theorem GlobalTheory.SS.DefectZero.mem_span_of_map_eq_zero (R A B D : Type) [CommRing R] [CommRing A] [CommRing B]
    [CommRing D] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra B D]
    [Algebra A D] [IsScalarTower A B D] (hs : Function.Surjective (algebraMap A B)) :
    ∃ ψ : D ⊗[A] Ω[A⁄R] →ₗ[D] D ⊗[B] Ω[B⁄R], LinearMap.ker ψ = Submodule.span D (Set.range
      fun h : RingHom.ker (algebraMap A B) => (1 : D) ⊗ₜ[A] KaehlerDifferential.D R A h.1) := by sorry
