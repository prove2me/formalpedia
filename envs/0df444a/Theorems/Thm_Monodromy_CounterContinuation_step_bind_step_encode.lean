-- Prove2me | Theorems.Thm_Monodromy_CounterContinuation_step_bind_step_encode
-- name    : Monodromy.CounterContinuation.step_bind_step_encode
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:47:39.615487+00:00
-- url     : https://prove2.me/theorems/b5ea2830-e360-431e-9f48-48604bd789c4
-- title:
--   Two native optional steps reproduce a source step, including halt
-- statement:
--   For every positive m, two-counter program P with m addresses, and natural-counter configuration s, taking a compiled optional step from encode(s) and binding its result to a second compiled step equals applying encode to the optional source result P.step(s). An absent first result propagates as absent, so the equality includes source halting as well as successful transitions.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.step`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.encode`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.step`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.step`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.encode`, `Monodromy.CounterContinuation.simulates`, `Monodromy.CounterContinuation.two_returns`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.step`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.step`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.encode`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.step`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.step`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.encode`, `Monodromy.CounterContinuation.simulates`, `Monodromy.CounterContinuation.two_returns`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.step`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.CounterContinuation.step_bind_step_encode at L484-L498 [UTF-8 22143:22922].

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
open Monodromy.CounterContinuation
variable {m : ℕ} [NeZero m]

theorem Monodromy.CounterContinuation.step_bind_step_encode (program : Counter.Program 2 m) (state : Counter.Configuration 2 m) :
    ((compile program).step (encode state)).bind (compile program).step =
      (Counter.step program state).map encode := by sorry
