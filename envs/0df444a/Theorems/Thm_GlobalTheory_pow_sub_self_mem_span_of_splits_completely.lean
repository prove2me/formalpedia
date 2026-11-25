-- Prove2me | Theorems.Thm_GlobalTheory_pow_sub_self_mem_span_of_splits_completely
-- name    : GlobalTheory.pow_sub_self_mem_span_of_splits_completely
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:41.400843+00:00
-- url     : https://prove2.me/theorems/128335bc-99e1-41f0-9bfa-c08ac904c5c3
-- title:
--   Global Theory: pow sub self mem span of splits completely
-- statement:
--   The Global Theory construction uses the pow sub self mem span of splits completely property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowSubSelfMemSpanOfSplitsCompletely.lean#L18-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowSubSelfMemSpanOfSplitsCompletely.lean#L18-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowSubSelfMemSpanOfSplitsCompletely
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory

theorem GlobalTheory.pow_sub_self_mem_span_of_splits_completely (E : Type) [Field E] [NumberField E] (g : ℕ)
    (hg : g.Prime)
    (hcard : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card =
      Module.finrank ℚ E)
    (hnd : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup)
    (x : 𝓞 E) : x ^ g - x ∈ Ideal.span {(g : 𝓞 E)} := by sorry
