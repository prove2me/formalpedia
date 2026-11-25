-- Prove2me | Theorems.Thm_GlobalTheory_LogExt_riemann_extension_log
-- name    : GlobalTheory.LogExt.riemann_extension_log
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:58.161186+00:00
-- url     : https://prove2.me/theorems/ca7fc84c-fb8f-45ae-93c3-1923e865d865
-- title:
--   Log Ext: riemann extension log
-- statement:
--   The Log Ext construction uses the riemann extension log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannExtensionOfLogGrowth.lean#L372-L505
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannExtensionOfLogGrowth.lean#L372-L505

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
open Filter Topology Asymptotics Metric Set Complex
open scoped Real
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem GlobalTheory.LogExt.riemann_extension_log (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (U : Set V) (φ u : V → ℂ) (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) (hu : DifferentiableOn ℂ u {b ∈ U | φ b ≠ 0})
    (hd : U ⊆ closure {b ∈ U | φ b ≠ 0})
    (hb : ∀ b₀ ∈ U, ∃ (C : ℝ) (k : ℕ),
      ∀ᶠ b in 𝓝 b₀, φ b ≠ 0 → ‖u b‖ ≤ C * (1 + |Real.log ‖φ b‖|) ^ k) :
    ∃ u' : V → ℂ, DifferentiableOn ℂ u' U ∧ Set.EqOn u' u {b ∈ U | φ b ≠ 0} := by sorry
