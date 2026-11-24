-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_Osc_exists_isOsc
-- name    : GlobalTheory.RealWeil.Osc.exists_isOsc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:20.294048+00:00
-- url     : https://prove2.me/theorems/3159d0f3-fabd-4c7a-a49a-9148abf089f5
-- title:
--   Osc: exists is Osc
-- statement:
--   The Osc construction uses the exists is Osc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionOfGaussianPairings.lean#L395-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionOfGaussianPairings.lean#L395-L418

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Osc
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ ρ' : V → B →L[ℂ] B}
set_option linter.unusedSectionVars false
variable {T : B →L[ℂ] B}

theorem GlobalTheory.RealWeil.Osc.exists_isOsc : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ (G : Type) [Group G] (k : G →* (V →L[ℝ] V)) (c : G → ℂ), (∀ g x y, omJ J (k g x) (k g y) = omJ J x y) → c 1 = 1 → (∀ g, star (c g) * c g * lam (k g) = 1) → (∀ g g', c g * c g' * mu J (k (g * g')) (k g) = c (g * g') * lam (k (g * g'))) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => k g v) Ω ∧ (∀ (Y : Type) [TopologicalSpace Y] (γ : Y → G), Continuous (fun y => k (γ y)) → Continuous (fun y => c (γ y)) → ∀ f, Sm ρ f → Continuous fun y => Ω (γ y) f) ∧ ∀ a g, (∀ x, ‖k g x‖ = ‖x‖) → ∀ f, Sm ρ f → ∫ u, gau u • ρ (k a u) f = f → Ω (a * g * a⁻¹) f = c g • f := by sorry
