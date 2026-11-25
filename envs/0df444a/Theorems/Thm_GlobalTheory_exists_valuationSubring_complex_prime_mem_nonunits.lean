-- Prove2me | Theorems.Thm_GlobalTheory_exists_valuationSubring_complex_prime_mem_nonunits
-- name    : GlobalTheory.exists_valuationSubring_complex_prime_mem_nonunits
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:46:49.41696+00:00
-- url     : https://prove2.me/theorems/16dc5978-e739-551d-b796-3d486312fe98
-- title:
--   Global Theory: exists valuation Subring complex prime mem nonunits
-- statement:
--   The Global Theory construction uses the exists valuation Subring complex prime mem nonunits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsValuationSubringComplexPrimeMemNonunits.lean#L5-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsValuationSubringComplexPrimeMemNonunits.lean#L5-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsValuationSubringComplexPrimeMemNonunits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_valuationSubring_complex_prime_mem_nonunits :
    ∀ p : ℕ, p.Prime → ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits := by sorry
