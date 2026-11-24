-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_axConstant_pos
-- name    : GroundTheory.PAdicHodge.axConstant_pos
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:29:29.35013+00:00
-- url     : https://prove2.me/theorems/15691bf0-0591-4e43-87fb-a378df2e56ff
-- title:
--   PAdic Hodge: ax Constant pos
-- statement:
--   The PAdic Hodge construction uses the ax Constant pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L447-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L447-L447

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
variable {p : ℕ} [hp : Fact p.Prime]

theorem GroundTheory.PAdicHodge.axConstant_pos : 0 < axConstant p := by sorry
