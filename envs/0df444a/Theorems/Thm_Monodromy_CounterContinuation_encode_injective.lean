-- Prove2me | Theorems.Thm_Monodromy_CounterContinuation_encode_injective
-- name    : Monodromy.CounterContinuation.encode_injective
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:34:46.083135+00:00
-- url     : https://prove2.me/theorems/030e6dec-cd56-4a22-a532-8f87f01086f3
-- title:
--   The continuation configuration encoding is injective
-- statement:
--   For every natural control size m, encoding a two-natural-counter configuration as the three-root state prepared from its two counter values and control label 3·pc is injective. Equality of encoded states therefore implies equality of the finite program counter and both counters; no positivity assumption on m is required.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.CounterContinuation.encode`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.CounterContinuation.encode`, `Monodromy.CounterContinuation.label`, `Monodromy.CounterContinuation.label_eq`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.prepare_injective`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.CounterContinuation.encode`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.CounterContinuation.encode`, `Monodromy.CounterContinuation.label`, `Monodromy.CounterContinuation.label_eq`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.prepare_injective`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.CounterContinuation.encode_injective at L329-L355 [UTF-8 13712:15024].

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
open CoupledContinuation
variable {m : ℕ}

theorem Monodromy.CounterContinuation.encode_injective : Function.Injective (@encode m) := by sorry
