-- Prove2me | Theorems.Thm_IntMul_CarryBatch_carry_batch
-- name    : IntMul.CarryBatch.carry_batch
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T12:56:20.111981+00:00
-- url     : https://prove2.me/theorems/90b9322c-e27c-4ed9-8570-d4a8bfb3fb9a
-- title:
--   Complete physical coefficient-list carry traversal with exact output and linear loop clock
-- statement:
--   Let $x_1,\ldots,x_m$ be binary coefficient words and $y$ an incoming carry word, all of width $n=\operatorname{val}(l)+1$. Write $B=\operatorname{val}(z)+1$ and assume $B\le n+1$. From an explicit prepared caller configuration, a fixed fifteen-tape machine processes the entire coefficient list and halts in its exact terminal configuration after at most
--
--   $$m\bigl(41n+13B+21|z|+4|l|+126\bigr)+3$$
--
--   physical transitions. Its emitted low digits and retained final carry agree with the ordinary base-$2^B$ carry scan. The input and accumulated output are retained with advanced cursors, descriptors and width templates are restored, and all temporary banks are empty with heads zero. The empty-list check and every coefficient restart are included in the bound. This result supplies the complete finite-state carry traversal needed after product coefficients have been generated; incoming data and descriptor preparation remain explicit caller obligations.
-- source:
--   Original complete actual finite-state coefficient carry traversal. Privately owns setup, full loop configuration invariant, arithmetic restarts, exact boundary dispatches, linear clock summation, binary encoding and abstract carry-scan agreement. Written by Codex.

import Definitions.Def_IntMul_CarryBatch
import Mathlib.Tactic
import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.Nat.Bits
import Definitions.Def_IntMul_CarryNormalization

open IntMul IntMul.CarryBatch

theorem IntMul.CarryBatch.carry_batch (pre : List Bool) (xs : List (List Bool)) (a y z l : List Bool)
    (hy : y.length=val l+1) (hx : ∀ w ∈ xs, w.length=val l+1)
    (hB : CarryStep.blockSize z ≤ val l+2) :
    ∃ t : ℕ, t ≤ xs.length*(41*(val l+1)+13*CarryStep.blockSize z+21*z.length+4*l.length+126)+3 ∧
      machine.step^[t] (initialFrame pre xs a y z l)=finalFrame pre xs a y z l ∧
      (machine.step^[t] (initialFrame pre xs a y z l)).state=machine.qHalt ∧
      (scanWords z xs y).1=
        (CarryNormalization.scan (2^CarryStep.blockSize z) (xs.map val) (val y)).1.flatMap
          (fun d => (bin (CarryStep.blockSize z) d).reverse) ∧
      val (scanWords z xs y).2=
        (CarryNormalization.scan (2^CarryStep.blockSize z) (xs.map val) (val y)).2 := by sorry
