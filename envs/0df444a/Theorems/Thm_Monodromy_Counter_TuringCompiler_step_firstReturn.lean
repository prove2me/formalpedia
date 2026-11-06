-- Prove2me | Theorems.Thm_Monodromy_Counter_TuringCompiler_step_firstReturn
-- name    : Monodromy.Counter.TuringCompiler.step_firstReturn
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:47:26.298267+00:00
-- url     : https://prove2.me/theorems/cc98de95-8e76-4847-b2b7-74483dbee9e9
-- title:
--   A Turing transition is a compiled first return
-- statement:
--   For positive a,q, every TM0 machine over Fin a and Fin q and every successful source transition s→t, the three-counter encodings satisfy the compiler’s FirstReturn relation: there is one successful compiled step from encode(s), followed by a finite possibly empty chain of compiled steps whose departure addresses are not source dispatches, ending at encode(t).
--
--   Statement dependencies: `Monodromy.Counter.TuringCompiler.FirstReturn`, `Monodromy.Counter.TuringCompiler.encode`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.TuringCompiler.FirstReturn`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.InternalStep`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.dispatch`, `Monodromy.Counter.TuringCompiler.encode`, `Monodromy.Counter.TuringCompiler.move_reaches`, `Monodromy.Counter.TuringCompiler.mulTarget`, `Monodromy.Counter.TuringCompiler.program`, `Monodromy.Counter.TuringCompiler.program_dispatch`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.Counter.TuringCompiler.write_step`, `Monodromy.Counter.step`, `Monodromy.TapeCode.encode`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.TuringCompiler.FirstReturn`, `Monodromy.Counter.TuringCompiler.encode`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.TuringCompiler.FirstReturn`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.InternalStep`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.counters`, `Monodromy.Counter.TuringCompiler.dispatch`, `Monodromy.Counter.TuringCompiler.encode`, `Monodromy.Counter.TuringCompiler.move_reaches`, `Monodromy.Counter.TuringCompiler.mulTarget`, `Monodromy.Counter.TuringCompiler.program`, `Monodromy.Counter.TuringCompiler.program_dispatch`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.Counter.TuringCompiler.write_step`, `Monodromy.Counter.step`, `Monodromy.TapeCode.encode`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.TuringCompiler.step_firstReturn at L1933-L1953 [UTF-8 92514:93773].

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
open Monodromy.Counter.TuringCompiler
open Turing
variable (a q : ℕ) [NeZero a] [NeZero q]

theorem Monodromy.Counter.TuringCompiler.step_firstReturn (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (source : TM0.step machine first = some last) :
    FirstReturn a q machine (encode a q first) (encode a q last) := by sorry
