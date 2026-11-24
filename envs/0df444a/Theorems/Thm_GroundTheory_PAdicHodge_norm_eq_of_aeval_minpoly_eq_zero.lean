-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_eq_of_aeval_minpoly_eq_zero
-- name    : GroundTheory.PAdicHodge.norm_eq_of_aeval_minpoly_eq_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:13.457841+00:00
-- url     : https://prove2.me/theorems/4869f9cb-2857-4712-b87f-5aba446e6a8f
-- title:
--   PAdic Hodge: norm eq of aeval minpoly eq zero
-- statement:
--   The PAdic Hodge construction uses the norm eq of aeval minpoly eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L292-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L292-L295

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
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
open Polynomial Module IntermediateField
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem GroundTheory.PAdicHodge.norm_eq_of_aeval_minpoly_eq_zero {y r : PadicAlgCl p}
    (h : aeval r (minpoly ℚ_[p] y) = 0) : ‖r‖ = ‖y‖ := by sorry
