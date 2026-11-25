-- Prove2me | Theorems.Thm_GlobalTheory_SharpGradient_rhF_sharp_gradient
-- name    : GlobalTheory.SharpGradient.rhF_sharp_gradient
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:05.94242+00:00
-- url     : https://prove2.me/theorems/5224ab5a-10b3-5e17-adf5-a188d847b712
-- title:
--   Sharp Gradient: rh F sharp gradient
-- statement:
--   The Sharp Gradient construction uses the rh F sharp gradient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ContinuousInvLeadingBlockEntry.lean#L412-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ContinuousInvLeadingBlockEntry.lean#L412-L419

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.SharpGradient.rhF_sharp_gradient : ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 →
    (∀ z ∈ OmF X x0, 0 ≤ rhF X x0 z ∧ ∀ ξ : Fin (nd X) → ℂ,
      Complex.normSq (∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) z * ξ j) ≤ rhF X x0 z * leviRh X x0 z ξ) ∧
    ∃ ρ C : ℝ, 0 < ρ ∧ ∀ z : V (nd X), ‖z‖ < ρ → z ∈ OmF X x0 ∧ rhF X x0 z ≤ C * ∑ e : Ent X,
      if (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ) then ‖z (Fintype.equivFin (Ent X) e)‖ ^ 2 else 0 := by sorry
