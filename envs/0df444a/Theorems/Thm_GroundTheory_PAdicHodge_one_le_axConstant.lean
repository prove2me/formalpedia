-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_one_le_axConstant
-- name    : GroundTheory.PAdicHodge.one_le_axConstant
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:47:27.100529+00:00
-- url     : https://prove2.me/theorems/aae8abde-e0ab-45e0-a0f4-8e164a69c3d7
-- title:
--   PAdic Hodge: one le ax Constant
-- statement:
--   The PAdic Hodge construction uses the one le ax Constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L443-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L443-L445

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

theorem GroundTheory.PAdicHodge.one_le_axConstant : 1 ≤ axConstant p := by sorry
