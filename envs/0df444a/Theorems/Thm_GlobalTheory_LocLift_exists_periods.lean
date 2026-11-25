-- Prove2me | Theorems.Thm_GlobalTheory_LocLift_exists_periods
-- name    : GlobalTheory.LocLift.exists_periods
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:51:07.707614+00:00
-- url     : https://prove2.me/theorems/5af8fee2-dfa6-5bb9-831b-b6c5a65f77f8
-- title:
--   Loc Lift: exists periods
-- statement:
--   The Loc Lift construction uses the exists periods property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HolomorphicMapModuliLiftsLocallyToPeriods.lean#L21-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HolomorphicMapModuliLiftsLocallyToPeriods.lean#L21-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolLinearLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TwoMulEqOfIsTypeFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicMapModuliLiftsLocallyToPeriods
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
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}

theorem GlobalTheory.LocLift.exists_periods
    (hLat : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (K : (Fin m → ℂ) → AddSubgroup (Fin g → ℂ)) (P : (Fin m → ℂ) → (La →+ (Fin g → ℂ))) (r : ℝ), IsOpen B → b₀ ∈ B → 0 < r → (∀ b ∈ B, ∀ z ∈ K b, ‖z‖ < r → z = 0) → (∀ (b : ℕ → (Fin m → ℂ)) (z : ℕ → (Fin g → ℂ)) (z₀ : Fin g → ℂ), Filter.Tendsto b Filter.atTop (nhds b₀) → Filter.Tendsto z Filter.atTop (nhds z₀) → (∀ i, z i ∈ K (b i)) → z₀ ∈ K b₀) → (∀ x, ContinuousAt (fun b => P b x) b₀) → (∀ b ∈ B, (P b).range ≤ K b) → (P b₀).range = K b₀ → Function.Injective (P b₀) → Submodule.span ℝ (Set.range (P b₀)) = ⊤ → ∀ᶠ b in nhds b₀, (P b).range = K b ∧ Function.Injective (P b) ∧ Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ DiscreteTopology (P b).range)
    [IsSeparated G.hom] {B : Set (Fin m → ℂ)} (hB : IsOpen B) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B)
    {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} (hy : IsHolTo B y) {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} {r : ℝ}
    (hr : 0 < r) (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left))
    (he : ∀ b ∈ B, IsExp (y b) (e b) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) (hl : HasLifts B y e)
    {La : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (P₀ : La →+ (Fin g → ℂ))
    (hi : Function.Injective P₀) (hs : Submodule.span ℝ (Set.range P₀) = ⊤) (hk : ∀ z, e b₀ z = 1 ↔ z ∈ P₀.range) :
    ∃ P : (Fin m → ℂ) → (La →+ (Fin g → ℂ)), P b₀ = P₀ ∧ ∀ᶠ b in 𝓝 b₀,
      (∀ x, DifferentiableAt ℂ (fun b => P b x) b) ∧ (∀ z, e b z = 1 ↔ z ∈ (P b).range) ∧
      Function.Injective (P b) ∧ Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ DiscreteTopology (P b).range := by sorry
