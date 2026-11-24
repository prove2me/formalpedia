-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_one_lt_prime_cast
-- name    : GroundTheory.PAdicHodge.one_lt_prime_cast
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:28:03.602438+00:00
-- url     : https://prove2.me/theorems/2ad3ac9e-0cdc-4ea0-85dd-b6002d883ca5
-- title:
--   PAdic Hodge: one lt prime cast
-- statement:
--   The PAdic Hodge construction uses the one lt prime cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L279-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L279-L279

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem GroundTheory.PAdicHodge.one_lt_prime_cast : (1 : ℝ) < p := by sorry
