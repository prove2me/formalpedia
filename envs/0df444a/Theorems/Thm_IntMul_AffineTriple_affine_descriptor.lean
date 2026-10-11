-- Prove2me | Theorems.Thm_IntMul_AffineTriple_affine_descriptor
-- name    : IntMul.AffineTriple.affine_descriptor
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T15:53:27.498312+00:00
-- url     : https://prove2.me/theorems/8e6ef94b-6f4f-4bbe-a644-6b1a2bcc165c
-- title:
--   Physical descriptor construction for three times the source value plus two
-- statement:
--   For any finite big-endian source word $w$, the fixed three-tape machine, starting with the actual marked source and empty output and scratch banks, halts in its exact final frame within
--
--   $$2|w|+4$$
--
--   actual transitions. It retains the source cells, returns the source head to its marker, leaves scratch empty, and writes a little-endian word $b$ whose output cursor is at its actual end and which satisfies
--
--   $$\operatorname{val}_{\mathrm{LE}}(b)=3\operatorname{val}(w)+2,\qquad |b|\le |w|+2.$$
--
--   The source may be empty or contain leading zeros. No numerical value or length is supplied to the machine. For the computed block-size-minus-one descriptor, this constructs the coefficient-precision-minus-one value $3B-1$.
-- source:
--   Original physical finite-carry descriptor transformation, full retained frame and explicit clock. Written by Codex.

import Definitions.Def_IntMul_AffineTriple
import Mathlib.Tactic

open IntMul IntMul.AffineTriple

theorem IntMul.AffineTriple.affine_descriptor (w : List Bool) :
    ∃ t : ℕ, t≤ 2*w.length+4 ∧ machine.step^[t] (initialFrame w)=finalFrame w ∧
      BinaryAdder.littleVal (triple 2 w.reverse)=3*val w+2 ∧
      (triple 2 w.reverse).length≤ w.length+2 := by sorry
