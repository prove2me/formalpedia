-- Prove2me | Theorems.Thm_GlobalTheory_SS_DefectZero_mem_span_of_residue
-- name    : GlobalTheory.SS.DefectZero.mem_span_of_residue
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:33:32.937399+00:00
-- url     : https://prove2.me/theorems/68c8722d-0c5e-4bf3-a269-a410dc32691b
-- title:
--   Defect Zero: mem span of residue
-- statement:
--   The Defect Zero construction uses the mem span of residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZero.lean#L184-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZero.lean#L184-L229

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

theorem GlobalTheory.SS.DefectZero.mem_span_of_residue {A D k M I I' : Type} [CommRing A] [CommRing D] [IsLocalRing D]
    [IsNoetherianRing D] [CommRing k] [Algebra A D] [Algebra D k] [Algebra A k]
    [IsScalarTower A D k] [AddCommGroup M] [Module A M] [Module.Finite A M] (π : D)
    (hπ : π ∈ IsLocalRing.maximalIdeal D) (hs : Function.Surjective (algebraMap D k))
    (hk : ∀ d, algebraMap D k d = 0 → π ∣ d) (g : I → M) (a : I' → I)
    (hsat : ∀ v, π • v ∈ Submodule.span D (Set.range fun i => (1 : D) ⊗ₜ[A] g i) →
      v ∈ Submodule.span D (Set.range fun i => (1 : D) ⊗ₜ[A] g i))
    (hsp : ∀ i, (1 : k) ⊗ₜ[A] g i ∈
      Submodule.span k (Set.range fun j => (1 : k) ⊗ₜ[A] g (a j))) (i : I) :
    (1 : D) ⊗ₜ[A] g i ∈ Submodule.span D (Set.range fun j => (1 : D) ⊗ₜ[A] g (a j)) := by sorry
