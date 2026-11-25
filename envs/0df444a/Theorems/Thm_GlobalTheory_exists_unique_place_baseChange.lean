-- Prove2me | Theorems.Thm_GlobalTheory_exists_unique_place_baseChange
-- name    : GlobalTheory.exists_unique_place_baseChange
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:56:10.010465+00:00
-- url     : https://prove2.me/theorems/cb289934-b97e-4f72-8e16-a9c2f9c3f0dd
-- title:
--   Global Theory: exists unique place base Change
-- statement:
--   The Global Theory construction uses the exists unique place base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L290-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L290-L396

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemIntegralClosureOfMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open PlaceExt

theorem GlobalTheory.exists_unique_place_baseChange : ∀ (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F'], Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' → Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L] [Algebra R L] [IsScalarTower R F L], (∀ x : F' ⊗[F] L, IsIntegral R' x ↔ x ∈ Submodule.span R' ((fun b : L => (1 : F') ⊗ₜ[F] b) '' (integralClosure R L : Set L))) → ∃ w' : ValPl.PlacesOver R L → AddValuation (F' ⊗[F] L) (WithTop ℤ), (∀ w (g : L), w' w ((1 : F') ⊗ₜ[F] g) = w.1 g) ∧ (∀ x : F' ⊗[F] L, IsIntegral R' x ↔ ∀ w, 0 ≤ w' w x) ∧ (∀ w (x : F' ⊗[F] L), 0 ≤ w' w x → ∃ g : L, 0 ≤ w.1 g ∧ 0 < w' w (x - (1 : F') ⊗ₜ[F] g)) ∧ ∀ (w : ValPl.PlacesOver R L) (u : AddValuation (F' ⊗[F] L) (WithTop ℤ)), (∀ g : L, u ((1 : F') ⊗ₜ[F] g) = w.1 g) → (∀ r : R', 0 ≤ u (algebraMap R' F' r ⊗ₜ[F] (1 : L))) → u = w' w := by sorry
