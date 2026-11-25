-- Prove2me | Theorems.Thm_GlobalTheory_KronOff_vanish_off
-- name    : GlobalTheory.KronOff.vanish_off
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:20:30.401953+00:00
-- url     : https://prove2.me/theorems/6362d5cf-061d-5b4e-9a41-c259d4a7e83d
-- title:
--   Kron Off: vanish off
-- statement:
--   The Kron Off construction uses the vanish off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableIndicatorOfContOn.lean#L234-L424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableIndicatorOfContOn.lean#L234-L424

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableIndicatorOfContOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.KronOff
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.KronOff.vanish_off : (MeasInvStatement (E := E)) → (VanishAtSStatement (E := E)) → (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (la L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ψ : Frame X.Ψ r → ℝ) (x0 x1 : Frame X.Ψ r) (bb δ : ℝ) (χ F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), 0 < nd X → IsOrth X x0 → IsOrth X x1 → X.IsSec L w0 → (∀ k, X.IsSec L (s k)) → ContinuousOn ψ X.dom → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → 0 ≤ bb → Metric.closedBall (0 : V (nd X)) δ ⊆ OmF X x0 → (∀ z, δ ≤ ‖z‖ → χ z = 0) → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z * (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ∂muF X x0 < ⊤ → (∀ z ∈ Metric.closedBall (0 : V (nd X)) δ, ∀ b ∈ Bor X.Ψ r, x1 ≠ rmul (cpt X x0 z) b) → w0 x1 ≠ 0 → (∀ k, s k x1 = 0) → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x1) z) / w0 (cpt X (x1) z) : V (nd X))) 0).det ≠ 0 → P x1 = 0) := by sorry
