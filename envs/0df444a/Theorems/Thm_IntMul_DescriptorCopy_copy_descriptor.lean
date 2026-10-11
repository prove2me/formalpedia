-- Prove2me | Theorems.Thm_IntMul_DescriptorCopy_copy_descriptor
-- name    : IntMul.DescriptorCopy.copy_descriptor
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T17:33:49.273976+00:00
-- url     : https://prove2.me/theorems/08ba7a4b-731d-43d0-bcd8-1b563de95a5b
-- title:
--   Physical retained-descriptor copy with both heads rewound and an exact linear clock
-- statement:
--   For every finite binary word $w$, a fixed three-tape finite routine starts with $w$ on source tape 1 and an empty destination tape 2, both heads at their actual markers. Original input cells and head are arbitrary and retained. In exactly
--
--   $$2|w|+3$$
--
--   actual transitions it reaches its globally halted final frame with exact copies of $w$ on tapes 1 and 2 and both heads at cell zero. Every bit is written and both heads are rewound physically; no payload or cursor jump is supplied at a phase boundary. Empty words and leading zeros are allowed. This routine supports placement of retained parameter descriptors into arithmetic work banks.
-- source:
--   Original physical binary descriptor copying and marker return with complete frame proof. Written by Codex.

import Definitions.Def_IntMul_DescriptorCopy
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

open IntMul IntMul.DescriptorCopy

theorem IntMul.DescriptorCopy.copy_descriptor (base : machine.Cfg) (w : List Bool) :
    machine.step^[2*w.length+3] (initialFrame base w)=finalFrame base w ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).state=machine.qHalt ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).cells machine.inTape=base.cells machine.inTape ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).head machine.inTape=base.head machine.inTape ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).cells 1=machine.tapeOf (w.map machine.bitSym) ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).cells 2=machine.tapeOf (w.map machine.bitSym) ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).head 1=0 ∧
      (machine.step^[2*w.length+3] (initialFrame base w)).head 2=0 := by sorry
