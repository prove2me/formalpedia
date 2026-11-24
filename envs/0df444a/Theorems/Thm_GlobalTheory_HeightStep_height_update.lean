-- Prove2me | Theorems.Thm_GlobalTheory_HeightStep_height_update
-- name    : GlobalTheory.HeightStep.height_update
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:17:16.715527+00:00
-- url     : https://prove2.me/theorems/8fe08ec9-8604-49b9-a382-2f7ff9ed3703
-- title:
--   Height Step: height update
-- statement:
--   The Height Step construction uses the height update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LatticeHeightUpdateFrameComponent.lean#L18-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LatticeHeightUpdateFrameComponent.lean#L18-L91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsMaximalMinorNeZeroOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatticeHeightUpdateFrameComponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.HeightStep
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.HeightStep.height_update : (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (d : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0) → ∀ (τ0 : X.Ψ) (W : Submodule E (Fin r → E)), ∃ M : Matrix (Fin r) (Fin (Module.finrank E W)) ℂ, 0 < (((M)ᴴ * (M)).det.re) ∧ ∀ a : Matrix (Fin r) (Fin r) ℂ, a.det ≠ 0 → d (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) W = d x W * ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) := by sorry
