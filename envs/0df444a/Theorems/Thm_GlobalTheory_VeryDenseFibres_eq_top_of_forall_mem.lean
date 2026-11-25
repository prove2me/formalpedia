-- Prove2me | Theorems.Thm_GlobalTheory_VeryDenseFibres_eq_top_of_forall_mem
-- name    : GlobalTheory.VeryDenseFibres.eq_top_of_forall_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:41:19.994679+00:00
-- url     : https://prove2.me/theorems/a500badd-46ed-5e02-8128-a6366ad6a276
-- title:
--   Very Dense Fibres: eq top of forall mem
-- statement:
--   The Very Dense Fibres construction uses the eq top of forall mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionAndGeometricallyConnect.lean#L94-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionAndGeometricallyConnect.lean#L94-L105

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedGenericFibreOfDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionAndGeometricallyConnect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.VeryDenseFibres

theorem GlobalTheory.VeryDenseFibres.eq_top_of_forall_mem {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R)
    [UniversallyClosed s] (P : Set (Ideal R))
    (hP : ∀ q : Ideal R, q.IsPrime → ∃ p ∈ P, p.IsPrime ∧ q ≤ p) (U : Z.Opens)
    (hU : ∀ z : Z, (s z).asIdeal ∈ P → z ∈ U) : U = ⊤ := by sorry
