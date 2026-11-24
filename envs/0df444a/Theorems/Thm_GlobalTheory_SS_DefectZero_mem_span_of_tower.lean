-- Prove2me | Theorems.Thm_GlobalTheory_SS_DefectZero_mem_span_of_tower
-- name    : GlobalTheory.SS.DefectZero.mem_span_of_tower
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:33:31.230001+00:00
-- url     : https://prove2.me/theorems/92decbba-4d2f-4b40-bae4-2a5523a9c51d
-- title:
--   Defect Zero: mem span of tower
-- statement:
--   The Defect Zero construction uses the mem span of tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZero.lean#L231-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZero.lean#L231-L239

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

theorem GlobalTheory.SS.DefectZero.mem_span_of_tower {A D K M I : Type} [CommRing A] [CommRing D] [CommRing K] [Algebra A D]
    [Algebra D K] [Algebra A K] [IsScalarTower A D K] [AddCommGroup M] [Module A M] (g : I → M)
    (m : M) (h : (1 : D) ⊗ₜ[A] m ∈ Submodule.span D (Set.range fun j => (1 : D) ⊗ₜ[A] g j)) :
    (1 : K) ⊗ₜ[A] m ∈ Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[A] g j) := by sorry
