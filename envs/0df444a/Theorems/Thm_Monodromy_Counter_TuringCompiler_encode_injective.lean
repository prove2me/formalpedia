-- Prove2me | Theorems.Thm_Monodromy_Counter_TuringCompiler_encode_injective
-- name    : Monodromy.Counter.TuringCompiler.encode_injective
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:32:45.231267+00:00
-- url     : https://prove2.me/theorems/23ac7fc7-fd14-4837-99ea-ae3ea0f32a6f
-- title:
--   The finite Turing configuration encoding is injective
-- statement:
--   For every positive alphabet size a and arbitrary natural state count q, the three-counter encoding of a TM0 configuration is injective. It stores the machine state and current tape symbol in the dispatch address, the left and right blank-tailed tape codes in counters 0 and 1 using base a+1, and 0 in the scratch counter. No nonzero assumption on q is required.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.TuringCompiler.encode`, `Monodromy.Counter.TuringCompiler.size`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.TuringCompiler.Row`, `Monodromy.Counter.TuringCompiler.dispatch_injective`, `Monodromy.Counter.TuringCompiler.encode`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.TapeCode.encode`, `Monodromy.TapeCode.encode_injective`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.TuringCompiler.encode`, `Monodromy.Counter.TuringCompiler.size`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.TuringCompiler.Row`, `Monodromy.Counter.TuringCompiler.dispatch_injective`, `Monodromy.Counter.TuringCompiler.encode`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.TapeCode.encode`, `Monodromy.TapeCode.encode_injective`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.TuringCompiler.encode_injective at L1537-L1561 [UTF-8 72553:73469].

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
omit [NeZero q]

theorem Monodromy.Counter.TuringCompiler.encode_injective : Function.Injective (encode a q) := by sorry
