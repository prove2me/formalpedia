-- Prove2me | Theorems.Thm_GlobalTheory_ProperFromMinimum_exists_compact
-- name    : GlobalTheory.ProperFromMinimum.exists_compact
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:22:16.080473+00:00
-- url     : https://prove2.me/theorems/0585e423-65ed-51d0-a980-5a941d7b2b09
-- title:
--   Proper From Minimum: exists compact
-- statement:
--   The Proper From Minimum construction uses the exists compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/BoundOfIneqs.lean#L42-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/BoundOfIneqs.lean#L42-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_FirstMinimumInvariantContinuousPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModelNefness
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_BoundOfIneqs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open GlobalTheory GlobalTheory.ProperFromMinimum

theorem GlobalTheory.ProperFromMinimum.exists_compact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (L eW : Wt X.Ψ r) (N a : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (et : Frame X.Ψ r → ℂ) (c i : ℝ) (ph : Frame X.Ψ r → ℝ), (∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ X.dom, X.la1 x < ε0 → ca / X.la1 x ^ 2 ≤ ph x) → InterpolationModelInequalities X L eW w et c i ph → (a : ℝ) * c < i → ∀ δ : ℝ, 0 < δ → ∃ C : Set (Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom, δ * (∑ k, X.pnorm L (w k) x ^ 2) ^ a ≤ X.pnorm eW et x ^ 2 → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C := by sorry
