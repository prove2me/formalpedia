-- Prove2me | Theorems.Thm_GlobalTheory_LogExt_exists_local_extension
-- name    : GlobalTheory.LogExt.exists_local_extension
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:00.46268+00:00
-- url     : https://prove2.me/theorems/f33001a4-6b38-438a-8e99-01abef62643f
-- title:
--   Log Ext: exists local extension
-- statement:
--   The Log Ext construction uses the exists local extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannExtensionOfLogGrowth.lean#L155-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannExtensionOfLogGrowth.lean#L155-L211

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannExtensionOfLogGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LogExt
open Filter Topology Asymptotics Metric Set Complex
open scoped Real
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem GlobalTheory.LogExt.exists_local_extension [FiniteDimensional ℂ V] {U : Set V} {φ u : V → ℂ} (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) (hu : DifferentiableOn ℂ u {b ∈ U | φ b ≠ 0})
    (hd : U ⊆ closure {b ∈ U | φ b ≠ 0})
    (hb : ∀ b₀ ∈ U, ∃ (C : ℝ) (k : ℕ),
      ∀ᶠ b in 𝓝 b₀, φ b ≠ 0 → ‖u b‖ ≤ C * (1 + |Real.log ‖φ b‖|) ^ k) {b₀ : V} (hb₀ : b₀ ∈ U) :
    ∃ w : V → ℂ, ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ w b ∧ (φ b ≠ 0 → w b = u b) := by sorry
