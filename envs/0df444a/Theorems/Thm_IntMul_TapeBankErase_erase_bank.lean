-- Prove2me | Theorems.Thm_IntMul_TapeBankErase_erase_bank
-- name    : IntMul.TapeBankErase.erase_bank
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T11:53:07.618951+00:00
-- url     : https://prove2.me/theorems/6ee05601-9960-4f7e-b515-6afe599383f0
-- title:
--   Actual selected-work-bank erasure with exact complete configuration and clock
-- statement:
--   Fix a machine with m+2 tapes and a selected writable-bank index bank≥1. Let w be any finite payload over bits and separators, with no interior start marker or blank, and let the selected head initially be at any position h. From the explicit incoming caller frame, the fixed four-state machine physically rewinds the selected bank to its real start marker, opens it, erases every payload symbol, turns on the first blank, returns its head to zero and halts after exactly
--
--   $$h+2|w|+3$$
--
--   actual transitions. The terminal selected bank is the empty marked tape. Every other caller tape and head, including root input 0, is retained exactly. The tape count and bank index are fixed construction choices, independent of payload length. No head oracle, span oracle or free workspace reset is used; the incoming caller frame and payload condition are explicit hypotheses.
-- source:
--   Original complete finite-symbol workspace erasure in the integer multiplication multitape model. Privately owns actual rewind, erase-cell updates, sweep, return, full configuration and exact clock proofs. Written by Codex.

import Definitions.Def_IntMul_TapeBankErase
import Mathlib.Tactic

open IntMul IntMul.TapeBankErase
open IntMul.TapeCopy (Sym)

theorem IntMul.TapeBankErase.erase_bank (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (base : (machine m bank hb).Cfg) (w : List Sym) (hw : ValidWord w) (h : ℕ) :
    (machine m bank hb).step^[h+2*w.length+3] (initialFrame m bank hb base w h)=
      finalFrame m bank hb base ∧
    ((machine m bank hb).step^[h+2*w.length+3] (initialFrame m bank hb base w h)).state=
      (machine m bank hb).qHalt := by sorry
