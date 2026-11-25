-- Prove2me | Theorems.Thm_GlobalTheory_ThetaValueCont_continuousAt_constant
-- name    : GlobalTheory.ThetaValueCont.continuousAt_constant
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:42:38.686258+00:00
-- url     : https://prove2.me/theorems/7305a095-3558-4549-90c5-0695f710d9eb
-- title:
--   Theta Value Cont: continuous At constant
-- statement:
--   The Theta Value Cont construction uses the continuous At constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCoordinatesOfRelations.lean#L49-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCoordinatesOfRelations.lean#L49-L171

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfFiniteOfClosedFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCoordinatesOfRelations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Set
open scoped Topology
open GlobalTheory GlobalTheory.ThetaValueCont
open GlobalTheory.ThetaFamily
open Filter Set
open scoped Topology

theorem GlobalTheory.ThetaValueCont.continuousAt_constant {V V' K ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] {B : Set V} {b₀ : V}
    {W : ι → Set (V × V')} {f : ι → V × V' → ℂ} {θ : K → V × V' → ℂ} {C : Set K} (hC : C.Finite) {κ : V → K}
    {c : V → ℂ} {r : ι → V → ℂ} (hW : ∀ j, IsOpen (W j)) (hWB : ∀ j, ∀ w ∈ W j, w.1 ∈ B)
    (hf : ∀ j, DifferentiableOn ℂ (f j) (W j)) (hθ : ∀ k ∈ C, ∀ j, DifferentiableOn ℂ (θ k) (W j))
    (hnz : ∀ k ∈ C, ∀ b ∈ B, ∀ z, ∃ᶠ w in 𝓝 z, θ k (b, w) ≠ 0) (hκ : ∀ b ∈ B, κ b ∈ C)
    (hq : ∀ j b z, (b, z) ∈ W j → ∃ ρ : V' → ℂ, ρ z ≠ 0 ∧ (z = 0 → ρ 0 = c b * r j b) ∧
      ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ρ w ∧ ρ w * θ (κ b) (b, w) = f j (b, w))
    (hB : B ∈ 𝓝 b₀) (cov : ∀ z, ∃ j, (b₀, z) ∈ W j)
    (uniq : ∀ k ∈ C, ∀ ρ : V' → ℂ, Differentiable ℂ ρ → (∀ z, ρ z ≠ 0) →
      (∀ z, ρ z * θ (κ b₀) (b₀, z) = θ k (b₀, z)) → k = κ b₀)
    (hr : ∀ j, (b₀, 0) ∈ W j → ContinuousAt (r j) b₀ ∧ r j b₀ ≠ 0) : ContinuousAt c b₀ := by sorry
