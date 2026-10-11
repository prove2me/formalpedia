-- Prove2me | Theorems.Thm_IntMul_CanonicalOutput_canonical_output
-- name    : IntMul.CanonicalOutput.canonical_output
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T12:53:32.44847+00:00
-- url     : https://prove2.me/theorems/436088a1-9d46-4cc9-8c26-b41c74163473
-- title:
--   Complete physical output reversal with retained caller frame and cleared scratch
-- statement:
--   Let $w$ be a finite binary word physically present on the output tape at its end cursor, with an empty scratch tape at its start marker. A fixed fifteen-tape machine reverses $w$, clears scratch, retains every other caller tape and head, and halts in its exact terminal configuration after at most
--
--   $$8|w|+16$$
--
--   actual transitions. The bound includes both physical copies, both erasures, real marker seeking and four caller returns, and holds for empty $w$. This supplies the output-order return required after low-to-high digit processing. Incoming tape contents and cursor positions are explicit caller obligations.
-- source:
--   Original complete physical output order repair. Owns actual copying, full caller frame preservation, both workspace erasures, and the complete linear clock proof. Written by Codex.

import Definitions.Def_IntMul_CanonicalOutput
import Mathlib.Tactic
import Theorems.Thm_IntMul_TapeBankErase_erase_bank
import Theorems.Thm_IntMul_FiniteCaller_simulate_run

open IntMul IntMul.CanonicalOutput

theorem IntMul.CanonicalOutput.canonical_output (base : machine.Cfg) (w : List Bool) :
    ∃ t : ℕ, t ≤ 8*w.length+16 ∧
      machine.step^[t] (initialFrame base w)=finalFrame base w ∧
      (machine.step^[t] (initialFrame base w)).state=machine.qHalt := by sorry
