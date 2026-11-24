-- Prove2me | Theorems.Thm_GlobalTheory_SubmodulePowSimple_snocZero_diag
-- name    : GlobalTheory.SubmodulePowSimple.snocZero_diag
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:24.816858+00:00
-- url     : https://prove2.me/theorems/ee93a471-1404-4001-abc0-9c9456197bd2
-- title:
--   Submodule Pow Simple: snoc Zero diag
-- statement:
--   The Submodule Pow Simple construction uses the snoc Zero diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubmodulePowSimpleEqSumEquivValues.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubmodulePowSimpleEqSumEquivValues.lean#L21-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubmodulePowSimpleEqSumEquivValues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule
open GlobalTheory GlobalTheory.SubmodulePowSimple
variable {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type}

theorem GlobalTheory.SubmodulePowSimple.snocZero_diag {m : ℕ} (b : Module.End ℂ P) (z : Fin m → P) :
    snocZero m (fun j => b (z j)) = fun j => b (snocZero m z j) := by sorry
