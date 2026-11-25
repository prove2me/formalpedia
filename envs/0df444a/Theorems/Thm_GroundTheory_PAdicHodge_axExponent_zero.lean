-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_axExponent_zero
-- name    : GroundTheory.PAdicHodge.axExponent_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:55.12056+00:00
-- url     : https://prove2.me/theorems/1808cac7-9a6b-4a07-9848-751299f546db
-- title:
--   PAdic Hodge: ax Exponent zero
-- statement:
--   The PAdic Hodge construction uses the ax Exponent zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L283-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L283-L283

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
omit hp

theorem GroundTheory.PAdicHodge.axExponent_zero : axExponent p 0 = 0 := by sorry
