-- Prove2me | Theorems.Thm_IntMul_TapeCopy_copy_first_operand
-- name    : IntMul.TapeCopy.copy_first_operand
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T18:05:48.474146+00:00
-- url     : https://prove2.me/theorems/96d40215-e3cd-4ff2-9e00-85ed1841c461
-- title:
--   First-operand copy in |x|+2 actual multitape transitions
-- statement:
--   For every pair of finite binary words $x,y$, the explicitly defined two-tape machine, started on the campaign-model input $x\#y$, is halted after $|x|+2$ transitions and its output tape is exactly the start marker followed by $x$, then blanks. No equality of operand lengths is required. This includes $x$ empty, where the machine produces empty output after two transitions. The alphabet, tape count, states, and transition table are all fixed independently of the input. In particular the routine has a linear transition bound $|x|+2\le2(|x|+1)$. This is a concrete tape-routing primitive, not a high-level list-operation cost assumption or a complete multiplier.
-- source:
--   Auxiliary operand-copy primitive for the integer-multiplication κ campaign. The machine model is IntMul_MultitapeModel: https://prove2.me/theorems/47ff1689-4e87-4af2-9406-674787e32429 , following A. Montanaro, Computational Complexity lecture notes (Cambridge, 2012), §3.4. The literal three-state transition table is this formalization’s implementation of the copy primitive, rather than a state table asserted by the paper.

import Definitions.Def_IntMul_TapeCopy
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

theorem IntMul.TapeCopy.copy_first_operand (x y : List Bool) :
    IntMul.TapeCopy.machine.HaltsWithOutput x y (x.length + 2) x := by sorry
