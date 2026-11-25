-- Prove2me | Theorems.Thm_GlobalTheory_FramePotential_frame_potential_basic
-- name    : GlobalTheory.FramePotential.frame_potential_basic
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:37.853971+00:00
-- url     : https://prove2.me/theorems/b58e4df8-1952-5a1b-91e8-2fc9f875a806
-- title:
--   Frame Potential: frame potential basic
-- statement:
--   The Frame Potential construction uses the frame potential basic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/OneLeMinorOfIsOrth.lean#L122-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/OneLeMinorOfIsOrth.lean#L122-L138

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OneLeMinorOfIsOrth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexOrder
open GlobalTheory GlobalTheory.FramePotential
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.FramePotential.frame_potential_basic :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → Measurable (fun x : Frame X.Ψ r => (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2)) ∧ (∀ x ∈ X.dom, 0 < (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ∧ (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, (∏ τ : X.Ψ, ‖dmin X.Gm (rmul x b) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (rmul x b) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) = (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2)) ∧ ∀ z ∈ OmF X x0, (∏ τ : X.Ψ, ‖dmin X.Gm (cpt X x0 z) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (cpt X x0 z) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) = Real.exp (-rhF X x0 z)) := by sorry
