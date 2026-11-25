-- Prove2me | Theorems.Thm_GlobalTheory_KronAssembly_kronHolPsi_of
-- name    : GlobalTheory.KronAssembly.kronHolPsi_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:36.051298+00:00
-- url     : https://prove2.me/theorems/fed4aa18-766c-5538-bf3c-d08176da8d24
-- title:
--   Kron Assembly: kron Hol Psi of
-- statement:
--   The Kron Assembly construction uses the kron Hol Psi of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/KronHolPsiOf.lean#L37-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/KronHolPsiOf.lean#L37-L163

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_KronHolPsiOf
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal

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
open GlobalTheory GlobalTheory.KronAssembly
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.KronAssembly.kronHolPsi_of :
    (ExtFStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s
        : Fin (nd X) → Frame X.Ψ r → ℂ), X.IsSec L w0 → (∀ k, X.IsSec L (s
        k)) → ∀ x ∈ X.dom, w0 x ≠ 0 → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2
        fun k => s k (cpt X (x) z) / w0 (cpt X (x) z) : V (nd X)))
        0).det ≠ 0 → ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2
        fun k => s k (cpt X (lact γ (rmul x b)) z) / w0 (cpt X (lact γ (rmul x b)) z) : V (nd X)))
        0).det ≠ 0) → (∀ (r : ℕ) (X : Data E r) (la
        : Wt X.Ψ r), ∀ ψ : Frame X.Ψ r → ℝ, IsInvFn X ψ → (∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ψ (cpt
        X x0 z)) (OmF X
        x0)) → (∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) → ContinuousOn ψ X.dom ∧ IsMetricW X la (X.dom.indicator
        fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) ∧ WLower X la (X.dom.indicator
        fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x))))) → (∀ (r : ℕ) (X : Data E r) (la
        L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ψ
        : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r) (bb m η
        : ℝ), 0 < nd X → IsOrth X x0 → X.IsSec L w0 → (∀ k, X.IsSec L (s
        k)) → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X
        x0) → 0 ≤ bb → bb < m → 0 < η → (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd
        X) → ℂ, m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ - (nd X
        : ℝ) * leviO X x0 (phla X L) z ξ + leviO X x0 ψ z ξ) → (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd
        X) → ℂ, 2 * η * leviO X x0 (phla X L) z ξ ≤ leviO X x0 (phla X
        la) z ξ - leviDens X x0 z ξ - (nd X : ℝ) * leviO X x0 (phla X
        L) z ξ + leviO X x0 ψ z ξ) → (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd
        X) → ℂ, ξ ≠ 0 → 0 < leviO X x0 (phla X L) z ξ) → w0 x0 ≠ 0 → (∀ k, s k x0 = 0) → (fderiv ℂ
        (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x0) z) / w0 (cpt X (x0) z) : V (nd
        X))) 0).det ≠ 0 → ∃ (ε : ℝ) (χ F : V (nd X) → ℂ), 0 < ε ∧ Metric.closedBall (0 : V (nd
        X)) (2 * ε) ⊆ OmF X x0 ∧ (∀ z ∈ Metric.closedBall (0 : V (nd X)) (2 * ε), (∀ k, s k (cpt X
        x0
        z) = 0) → z = 0) ∧ Continuous χ ∧ (∀ z, ‖z‖ ≤ ε → χ z = 1) ∧ (∀ z, 2 * ε ≤ ‖z‖ → χ z = 0) ∧ DifferentiableOn ℂ F (OmF
        X x0) ∧ ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt
        X x0 z))) / kaF X x0 bb z * (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X
        : ℝ))) ∂muF X x0 < ⊤) → (∀ (r : ℕ) (X : Data E r) (la L : Wt X.Ψ r) (w0
        : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ψ : Frame X.Ψ r → ℝ) (x0 x1
        : Frame X.Ψ r) (bb δ : ℝ) (χ F : V (nd X) → ℂ) (P
        : Frame X.Ψ r → ℂ), 0 < nd X → IsOrth X x0 → IsOrth X x1 → X.IsSec L w0 → (∀ k, X.IsSec L (s
        k)) → ContinuousOn ψ X.dom → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x
        b) = ψ x) → 0 ≤ bb → Metric.closedBall (0 : V (nd
        X)) δ ⊆ OmF X x0 → (∀ z, δ ≤ ‖z‖ → χ z = 0) → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0
        z) = F z) → ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * Real.exp (-(phla X la (cpt X x0 z) + ψ
        (cpt X x0 z))) / kaF X x0 bb z * (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X
        : ℝ))) ∂muF X x0 < ⊤ → (∀ z ∈ Metric.closedBall (0 : V (nd
        X)) δ, ∀ b ∈ Bor X.Ψ r, x1 ≠ rmul (cpt X x0 z) b) → w0 x1 ≠ 0 → (∀ k, s k x1 = 0) → (fderiv
        ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x1) z) / w0 (cpt X (x1)
        z) : V (nd X))) 0).det ≠ 0 → P x1 = 0) → (∀ (r : ℕ) (X : Data E r) (la L : Wt X.Ψ r) (w0
        : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ψ : Frame X.Ψ r → ℝ) (x0
        : Frame X.Ψ r) (bb ε δ : ℝ) (χ F : V (nd
        X) → ℂ), 0 < nd X → IsOrth X x0 → X.IsBddSec L w0 → (∀ k, X.IsBddSec L (s
        k)) → ContinuousOn ψ X.dom → (∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) → 0 ≤ bb → 0 < ε → Metric.closedBall (0
        : V (nd
        X)) δ ⊆ OmF X x0 → Continuous χ → (∀ z, ‖z‖ ≤ ε → χ z = 1) → (∀ z, δ ≤ ‖z‖ → χ z = 0) → DifferentiableOn ℂ F (OmF
        X x0) → ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt
        X x0 z))) / kaF X x0 bb z * (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X
        : ℝ))) ∂muF X x0 < ⊤ → w0 x0 ≠ 0 → (∀ k, s k x0 = 0) → (fderiv ℂ (fun z : V (nd
        X) => (WithLp.toLp 2 fun k => s k (cpt X (x0) z) / w0 (cpt X (x0) z) : V (nd X)))
        0).det ≠ 0 → F 0 = 1 ∧ InAt X x0 (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla
        X la x + ψ x)))) bb F ∧ ∀ C : Set (Frame X.Ψ
        r), IsCompact C → C ⊆ X.dom → ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp
        (-phla X la (cpt X x0 z))) ∂muF X x0 < ⊤) → (KronHolPsiStatement (E := E)) := by sorry
