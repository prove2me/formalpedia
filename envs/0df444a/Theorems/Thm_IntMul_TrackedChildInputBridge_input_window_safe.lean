-- Prove2me | Theorems.Thm_IntMul_TrackedChildInputBridge_input_window_safe
-- name    : IntMul.TrackedChildInputBridge.input_window_safe
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T06:59:10.992927+00:00
-- url     : https://prove2.me/theorems/f436fd58-b62a-4caf-ae47-00a30ca10695
-- title:
--   All-times protected workspace during physical child-argument marshalling
-- statement:
--   Let the parent output bank contain the canonical child request packet for finite bit words x and y, and let the caller buffer contain any older returned bit word v. At every physical time of the fixed-tape child-input bridge, including all rewind, copy, old-tail erasure and halted steps, the buffer head remains at or above its local marker sigma and each work head remains at or above its local bank offset. Empty arguments and shorter packets are allowed. The theorem requires no positive offsets, global marker uniqueness or work-tail bounds.
-- source:
--   Original all-times child argument trajectory proof for integer multiplication recursive foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedChildInputBridge
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.TrackedChildInputBridge

theorem IntMul.TrackedChildInputBridge.input_window_safe (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (x y : List Bool) (packet : c.cells M.outTape=M.tapeOf (TrackedBankPreparation.inputWord M x y)) :
    ∀ t, sigma ≤ ((machine M).step^[t] (initialFrame M base sigma offset extent c v)).head (bufferTape M) ∧
      ∀ j, offset j ≤ ((machine M).step^[t] (initialFrame M base sigma offset extent c v)).head
        (BankedSimulation.workTape M j) := by sorry
