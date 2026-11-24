-- Prove2me | Theorems.Thm_GlobalTheory_LocalGrouping_ne_zero_of_finprod_mem_ne_zero
-- name    : GlobalTheory.LocalGrouping.ne_zero_of_finprod_mem_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:13:48.06542+00:00
-- url     : https://prove2.me/theorems/67db01e8-7bd2-4b2c-96b2-4453ccfe1846
-- title:
--   Local Grouping: ne zero of finprod mem ne zero
-- statement:
--   The Local Grouping construction uses the ne zero of finprod mem ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumRestrictedProductCount.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumRestrictedProductCount.lean#L9-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumRestrictedProductCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open scoped Classical
open GlobalTheory GlobalTheory.LocalGrouping
open Function

theorem GlobalTheory.LocalGrouping.ne_zero_of_finprod_mem_ne_zero {ι : Type} (S : Set ι) (h : ι → ℂ)
    (hf : (mulSupport h).Finite) (hne : ∏ᶠ i ∈ S, h i ≠ 0) : ∀ i ∈ S, h i ≠ 0 := by sorry
