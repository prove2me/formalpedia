-- Prove2me | Theorems.Thm_GlobalTheory_SubmodulePowSimple_single_diag
-- name    : GlobalTheory.SubmodulePowSimple.single_diag
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:22.67832+00:00
-- url     : https://prove2.me/theorems/b1371f5a-4e3a-40ce-a29a-9513efaeed06
-- title:
--   Submodule Pow Simple: single diag
-- statement:
--   The Submodule Pow Simple construction uses the single diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubmodulePowSimpleEqSumEquivValues.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubmodulePowSimpleEqSumEquivValues.lean#L25-L30

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

theorem GlobalTheory.SubmodulePowSimple.single_diag {m : ℕ} (b : Module.End ℂ P) (p : P) :
    (Pi.single (Fin.last m) (b p) : Fin (m+1) → P) = fun j => b ((Pi.single (Fin.last m) p : Fin (m+1) → P) j) := by sorry
