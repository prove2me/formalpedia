-- Prove2me | Theorems.Thm_GlobalTheory_PuncturedDiscExtension_analyticAt_update_of_bdd
-- name    : GlobalTheory.PuncturedDiscExtension.analyticAt_update_of_bdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:11.360246+00:00
-- url     : https://prove2.me/theorems/24f18eec-7c9a-47c1-a067-f02994b75dab
-- title:
--   Punctured Disc Extension: analytic At update of bdd
-- statement:
--   The Punctured Disc Extension construction uses the analytic At update of bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExtensionAcrossZeroOfExpTwoPiIBound.lean#L6-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExtensionAcrossZeroOfExpTwoPiIBound.lean#L6-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExtensionAcrossZeroOfExpTwoPiIBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
open GlobalTheory GlobalTheory.PuncturedDiscExtension

theorem GlobalTheory.PuncturedDiscExtension.analyticAt_update_of_bdd {F : ℂ → ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ F z)
    (hb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖F z‖ ≤ B) :
    AnalyticAt ℂ (Function.update F 0 (limUnder (𝓝[≠] (0:ℂ)) F)) 0 := by sorry
