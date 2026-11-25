-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_axExponent_le
-- name    : GroundTheory.PAdicHodge.axExponent_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:50.90357+00:00
-- url     : https://prove2.me/theorems/df9e6eed-5a54-402c-b0f8-17a27d65869d
-- title:
--   PAdic Hodge: ax Exponent le
-- statement:
--   The PAdic Hodge construction uses the ax Exponent le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L295-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L295-L300

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

theorem GroundTheory.PAdicHodge.axExponent_le (k : ℕ) : axExponent p k ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by sorry
