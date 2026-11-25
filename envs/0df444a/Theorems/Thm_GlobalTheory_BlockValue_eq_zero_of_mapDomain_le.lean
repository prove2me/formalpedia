-- Prove2me | Theorems.Thm_GlobalTheory_BlockValue_eq_zero_of_mapDomain_le
-- name    : GlobalTheory.BlockValue.eq_zero_of_mapDomain_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:52:51.979853+00:00
-- url     : https://prove2.me/theorems/ed850d1d-5c46-493c-958a-5a65e45721f9
-- title:
--   Block Value: eq zero of map Domain le
-- statement:
--   The Block Value construction uses the eq zero of map Domain le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BlockValueOnRowsEq.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BlockValueOnRowsEq.lean#L56-L60

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open scoped BigOperators
open GlobalTheory GlobalTheory.BlockValue
variable {C : Type} [Field C] {σ κ : Type}

theorem GlobalTheory.BlockValue.eq_zero_of_mapDomain_le (π : σ → κ) {m : σ →₀ ℕ} (h : m.mapDomain π ≤ 0) : m = 0 := by sorry
