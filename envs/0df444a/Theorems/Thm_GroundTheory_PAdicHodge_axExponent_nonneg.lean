-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_axExponent_nonneg
-- name    : GroundTheory.PAdicHodge.axExponent_nonneg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:43.835186+00:00
-- url     : https://prove2.me/theorems/65992084-c700-4bc2-b05b-1f76c6abc963
-- title:
--   PAdic Hodge: ax Exponent nonneg
-- statement:
--   The PAdic Hodge construction uses the ax Exponent nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L310-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L310-L312

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

theorem GroundTheory.PAdicHodge.axExponent_nonneg (k : ℕ) : 0 ≤ axExponent p k := by sorry
