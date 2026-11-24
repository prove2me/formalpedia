-- Prove2me | Theorems.Thm_GlobalTheory_PuncturedDiscExtension_bdd_of_re_le
-- name    : GlobalTheory.PuncturedDiscExtension.bdd_of_re_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:58:34.075703+00:00
-- url     : https://prove2.me/theorems/1e2d1321-26df-4cc1-80b5-9d0a262f9441
-- title:
--   Punctured Disc Extension: bdd of re le
-- statement:
--   The Punctured Disc Extension construction uses the bdd of re le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExtensionAcrossZeroOfExpTwoPiIBound.lean#L25-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExtensionAcrossZeroOfExpTwoPiIBound.lean#L25-L97

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

theorem GlobalTheory.PuncturedDiscExtension.bdd_of_re_le {F : ℂ → ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ F z)
    {M : ℝ} (hM : ∀ᶠ z in 𝓝[≠] (0:ℂ), (F z).re ≤ M) :
    ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖F z‖ ≤ B := by sorry
