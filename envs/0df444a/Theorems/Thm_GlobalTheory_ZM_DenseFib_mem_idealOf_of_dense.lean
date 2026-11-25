-- Prove2me | Theorems.Thm_GlobalTheory_ZM_DenseFib_mem_idealOf_of_dense
-- name    : GlobalTheory.ZM.DenseFib.mem_idealOf_of_dense
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:04:47.966746+00:00
-- url     : https://prove2.me/theorems/62e0b553-41dc-4154-927e-b9fe55c05ab5
-- title:
--   Dense Fib: mem ideal Of of dense
-- statement:
--   The Dense Fib construction uses the mem ideal Of of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MemIdealOfOfDense.lean#L66-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MemIdealOfOfDense.lean#L66-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MemIdealOfOfDense
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
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.DenseFib

theorem GlobalTheory.ZM.DenseFib.mem_idealOf_of_dense : ∀ (R σ : Type) [CommRing R] (Y : Scheme.{0}) (s : Y ⟶ Sp R) (N : LB Y) (ty : σ → N.Sec) (Sg : Set (Sp R)) (F : MvPolynomial σ R) (e : ℕ), IsReduced Y → Flat s → LocallyOfFinitePresentation s → N.IsLB → Dense Sg → F.IsHomogeneous e → (∀ (K : Type) [Field K] [IsAlgClosed K] (β : R →+* K) (y : Sp K ⟶ Y) (v : σ → K), y ≫ s = spMap β → Set.range (spMap β) ⊆ Sg → SecCoord N ty y v → MvPolynomial.eval₂ β v F = 0) → F ∈ idealOf s N ty (𝟙 Y) := by sorry
