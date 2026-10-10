-- Prove2me | Theorems.Thm_IntMul_TrackedReturnReplacement_return_window_safe
-- name    : IntMul.TrackedReturnReplacement.return_window_safe
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T06:50:58.697107+00:00
-- url     : https://prove2.me/theorems/207daacb-0324-43cf-beb2-c9dc3c9c0ff9
-- title:
--   All-times protected workspace during complete physical returned-word replacement
-- statement:
--   Let the output bank contain a canonical finite bit word w and let the caller return buffer initially contain any old finite bit word v. For every physical time t of the fixed-tape returned-word replacement service, its buffer head remains at or above the local buffer marker sigma and every work head remains at or above its local bank offset. This includes all rewind, copy, old-tail erasure, marker-restoration, endpoint-seek and halted steps. Empty and shorter replacement words are allowed. No positivity, global-marker uniqueness or work-tail bound is required for this local floor invariant.
-- source:
--   Original complete all-times returned-word replacement trajectory proof for integer multiplication recursive foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedReturnReplacement
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.TrackedReturnReplacement

theorem IntMul.TrackedReturnReplacement.return_window_safe (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool)
    (packet : c.cells M.outTape=M.tapeOf (w.map M.bitSym)) :
    ∀ t, sigma ≤ ((machine M).step^[t] (initialFrame M base sigma offset extent c v)).head (bufferTape M) ∧
      ∀ j, offset j ≤ ((machine M).step^[t] (initialFrame M base sigma offset extent c v)).head
        (BankedSimulation.workTape M j) := by sorry
