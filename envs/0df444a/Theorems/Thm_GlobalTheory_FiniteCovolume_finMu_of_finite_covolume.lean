-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCovolume_finMu_of_finite_covolume
-- name    : GlobalTheory.FiniteCovolume.finMu_of_finite_covolume
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:45.56626+00:00
-- url     : https://prove2.me/theorems/aea63673-09aa-48ef-8ec0-45e1487662a5
-- title:
--   Finite Covolume: fin Mu of finite covolume
-- statement:
--   The Finite Covolume construction uses the fin Mu of finite covolume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FinMuOfFiniteCovolume.lean#L369-L486
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FinMuOfFiniteCovolume.lean#L369-L486

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FinMuOfFiniteCovolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.FiniteCovolume
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.FiniteCovolume.finMu_of_finite_covolume :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ, (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ((∀ (r : ℕ) (X : Data E r), ∃ H : Subgroup (X.Ψ → GL (Fin r) ℂ), ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) ∧ (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → LocallyCompactSpace H ∧ SecondCountableTopology H ∧ ∀ x0, IsOrth X x0 → (∀ g : H, IsOrth X (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) ∧ ∃ ι : Frame X.Ψ r → H, ContinuousOn ι {x | IsOrth X x} ∧ (∀ x, IsOrth X x → X.lmulC (fun τ => ((ι x : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 = x) ∧ ∀ g : H, ι (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = g)) → (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H] (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ ν : Measure H, ν.IsMulLeftInvariant ∧ IsFiniteMeasureOnCompacts ν ∧ ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) → ∫⁻ g, φ (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) ∂ν = ∫⁻ z, φ (cpt X x0 z) ∂muF X x0) → (∀ (r : ℕ) (X : Data E r), PropDisc X) → (∀ (r : ℕ) (X : Data E r), FinMu X) := by sorry
