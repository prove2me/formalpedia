-- Prove2me | Theorems.Thm_Monodromy_CounterMultiplication_consume_reach
-- name    : Monodromy.CounterMultiplication.consume_reach
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:34:59.832201+00:00
-- url     : https://prove2.me/theorems/ed31c53f-cd9a-496d-a904-be9861812430
-- title:
--   Multiplication consumption accumulates the scaled input
-- statement:
--   For all natural factor f and counter values x,y, including f=0, the fixed two-counter multiplication program has a finite run from control address 0 with counters (x,y) to address 0 with counters (0,y+f·x). Reachability is reflexive-transitive and imposes no positive-length or halting condition.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.step`, `Monodromy.CounterMultiplication.configuration`, `Monodromy.CounterMultiplication.program`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.step`, `Monodromy.CounterMultiplication.configuration`, `Monodromy.CounterMultiplication.increments_reach`, `Monodromy.CounterMultiplication.phase`, `Monodromy.CounterMultiplication.program`, `Monodromy.CounterMultiplication.step_consume`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.step`, `Monodromy.CounterMultiplication.configuration`, `Monodromy.CounterMultiplication.program`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.step`, `Monodromy.CounterMultiplication.configuration`, `Monodromy.CounterMultiplication.increments_reach`, `Monodromy.CounterMultiplication.phase`, `Monodromy.CounterMultiplication.program`, `Monodromy.CounterMultiplication.step_consume`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.CounterMultiplication.consume_reach at L998-L1016 [UTF-8 46452:47499].

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
open Monodromy.CounterMultiplication

theorem Monodromy.CounterMultiplication.consume_reach (factor first second : ℕ) :
    StateTransition.Reaches (Counter.step (program factor))
      (configuration factor 0 first second)
      (configuration factor 0 0 (second + factor * first)) := by sorry
