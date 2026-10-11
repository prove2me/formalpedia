-- Prove2me | Theorems.Thm_IntMul_CarryOutput_carry_output
-- name    : IntMul.CarryOutput.carry_output
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T13:03:06.712362+00:00
-- url     : https://prove2.me/theorems/5a7c66dd-edf4-4c67-8827-5f610b6daba6
-- title:
--   Complete physical carry normalization and big-endian output return with linear clock
-- statement:
--   Let $x_1,\ldots,x_m$ be binary coefficient words and $y$ a saved carry word, all of width $n=\operatorname{val}(l)+1$. Let $B=\operatorname{val}(z)+1$ satisfy $B\le n+1$, and let $a$ be the accumulated little-endian output prefix. From the explicit prepared caller configuration, a fixed fifteen-tape machine processes all coefficients, physically reverses the accumulated low-digit output to big-endian order, clears scratch, and globally halts after at most
--
--   $$m\bigl(41n+21B+21|z|+4|l|+126\bigr)+8|a|+21$$
--
--   actual transitions. The exact output word is the reversal of the concatenation of $a$ and the little-endian digits of the ordinary base-$2^B$ carry scan, and the retained final carry agrees with that scan. The entire terminal configuration retains the read-only input, descriptors, width templates, and saved carry; temporary banks are empty. All copies, arithmetic operations, erasures, rewinds and caller returns are included. This realizes the physical carry/output stage after coefficient generation; global input and descriptor preparation remain explicit caller obligations.
-- source:
--   Original complete same-tape physical carry/output composition. Owns native finite-state embeddings, step/run preservation, exact final-frame handoffs, output widths and complete charged clock. Written by Codex.

import Definitions.Def_IntMul_CarryOutput
import Mathlib.Tactic
import Definitions.Def_IntMul_CarryNormalization

open IntMul IntMul.CarryOutput

theorem IntMul.CarryOutput.carry_output (pre : List Bool) (xs : List (List Bool)) (a y z l : List Bool)
    (hy : y.length=val l+1) (hx : ∀ w ∈ xs, w.length=val l+1)
    (hB : CarryStep.blockSize z ≤ val l+2) :
    ∃ t : ℕ,
      t ≤ xs.length*(41*(val l+1)+21*CarryStep.blockSize z+21*z.length+4*l.length+126)+8*a.length+21 ∧
      machine.step^[t] (initialFrame pre xs a y z l)=finalFrame pre xs a y z l ∧
      (machine.step^[t] (initialFrame pre xs a y z l)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame pre xs a y z l)).cells 1=
        machine.tapeOf
          ((a++(CarryNormalization.scan (2^CarryStep.blockSize z)
            (xs.map val) (val y)).1.flatMap
              (fun d => (bin (CarryStep.blockSize z) d).reverse)).reverse.map machine.bitSym) ∧
      val (CarryBatch.scanWords z xs y).2=
        (CarryNormalization.scan (2^CarryStep.blockSize z) (xs.map val) (val y)).2 := by sorry
