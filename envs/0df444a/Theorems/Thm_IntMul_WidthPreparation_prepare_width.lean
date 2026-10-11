-- Prove2me | Theorems.Thm_IntMul_WidthPreparation_prepare_width
-- name    : IntMul.WidthPreparation.prepare_width
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T13:50:13.265307+00:00
-- url     : https://prove2.me/theorems/2ce53452-4416-4063-a680-598f687f582d
-- title:
--   Complete physical preparation of retained width descriptor and both counter templates
-- statement:
--   Let $d$ be a finite binary word physically retained on descriptor bank 15, with empty counter/template banks 3 and 4 and all three heads at their real start markers. A fixed sixteen-tape machine copies $d$ into both counter banks, writes their separator delimiters, places both counter heads at their least-significant-bit positions, rewinds the retained descriptor and halts in its exact terminal caller configuration after exactly
--
--   $$2|d|+4$$
--
--   actual transitions. Every other caller tape and head, including input and output, is retained. The result covers empty descriptors. This is the physically charged preparation required between coefficient product recovery and fixed-width output return; presence of the retained descriptor and empty destination banks remains an explicit incoming caller obligation.
-- source:
--   Original complete physical width-descriptor preparation. Owns opening, delimiter writes, simultaneous copies, retained frames, actual marker rewind and exact clock. Written by Codex.

import Definitions.Def_IntMul_WidthPreparation
import Mathlib.Tactic

open IntMul IntMul.WidthPreparation

theorem IntMul.WidthPreparation.prepare_width (base : machine.Cfg) (d : List Bool) :
    machine.step^[2*d.length+4] (initialFrame base d)=finalFrame base d ∧
      (machine.step^[2*d.length+4] (initialFrame base d)).state=machine.qHalt := by sorry
