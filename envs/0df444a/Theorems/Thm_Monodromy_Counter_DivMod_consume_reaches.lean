-- Prove2me | Theorems.Thm_Monodromy_Counter_DivMod_consume_reaches
-- name    : Monodromy.Counter.DivMod.consume_reaches
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:28:07.991194+00:00
-- url     : https://prove2.me/theorems/64df983c-714d-4afc-b9f8-57dc21e010e1
-- title:
--   Division consumption accumulates quotient and control remainder
-- statement:
--   For every positive divisor p, natural counter values x,y, and remainder r with 0≤r<p, the finite division program runs from its consume(r) address with counters (x,y) to transfer((x+r) mod p) with counters (0,y+⌊(x+r)/p⌋). The remainder is retained in finite control, and the conclusion is finite reachability rather than termination at that transfer address.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.DivMod.configuration`, `Monodromy.Counter.DivMod.consume`, `Monodromy.Counter.DivMod.program`, `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.DivMod.size`, `Monodromy.Counter.DivMod.transfer`, `Monodromy.Counter.step`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.DivMod.bump`, `Monodromy.Counter.DivMod.configuration`, `Monodromy.Counter.DivMod.consume`, `Monodromy.Counter.DivMod.next`, `Monodromy.Counter.DivMod.prepend`, `Monodromy.Counter.DivMod.program`, `Monodromy.Counter.DivMod.reaches_step`, `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.DivMod.residue_small`, `Monodromy.Counter.DivMod.size`, `Monodromy.Counter.DivMod.step_bump`, `Monodromy.Counter.DivMod.step_consume_succ`, `Monodromy.Counter.DivMod.step_consume_zero`, `Monodromy.Counter.DivMod.transfer`, `Monodromy.Counter.step`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.DivMod.configuration`, `Monodromy.Counter.DivMod.consume`, `Monodromy.Counter.DivMod.program`, `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.DivMod.size`, `Monodromy.Counter.DivMod.transfer`, `Monodromy.Counter.step`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.DivMod.bump`, `Monodromy.Counter.DivMod.configuration`, `Monodromy.Counter.DivMod.consume`, `Monodromy.Counter.DivMod.next`, `Monodromy.Counter.DivMod.prepend`, `Monodromy.Counter.DivMod.program`, `Monodromy.Counter.DivMod.reaches_step`, `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.DivMod.residue_small`, `Monodromy.Counter.DivMod.size`, `Monodromy.Counter.DivMod.step_bump`, `Monodromy.Counter.DivMod.step_consume_succ`, `Monodromy.Counter.DivMod.step_consume_zero`, `Monodromy.Counter.DivMod.transfer`, `Monodromy.Counter.step`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.DivMod.consume_reaches at L1181-L1216 [UTF-8 55527:57724].

module
public import Definitions.Def_Monodromy_Counter
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.DivMod
variable (p : ℕ) [NeZero p]

theorem Monodromy.Counter.DivMod.consume_reaches (first second : ℕ) (remainder : Fin p) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (consume p remainder) first second)
      (configuration p (transfer p (residue p (first + remainder.val))) 0
        (second + (first + remainder.val) / p)) := by sorry
