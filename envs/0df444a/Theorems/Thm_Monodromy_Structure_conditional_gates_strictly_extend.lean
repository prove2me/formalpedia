-- Prove2me | Theorems.Thm_Monodromy_Structure_conditional_gates_strictly_extend
-- name    : Monodromy.Structure.conditional_gates_strictly_extend
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:49:55.649576+00:00
-- url     : https://prove2.me/theorems/042d5d0a-1341-43b0-a47e-df2989615a40
-- title:
--   Deleting Both Conditional Gates Strictly Reduces Fixed-Interface Realizability
-- statement:
--   There exists a partial function f:ℕ→Part ℕ realized by some positive-degree native Program under the fixed inputLabels/outputLabels interface, but realized by no positive-degree program whose every table word contains neither zeroLeft nor zeroRight in either direction. Arbitrary finite routing, stopping bits and the remaining signed gates are still allowed in the restricted language.
--
--   Statement dependencies: `Monodromy.Structure.ProbeFreeRealizable`, `Monodromy.Structure.Realizable`.
--
--   Original proof dependencies: `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.ProbeFree`, `Monodromy.ForwardBoundary.hardFunction`, `Monodromy.ForwardBoundary.hardFunction_partrec`, `Monodromy.Structure.Computes`, `Monodromy.Structure.ProbeFreeRealizable`, `Monodromy.Structure.Realizable`, `Monodromy.Structure.no_probeFree_hardFunction`, `Monodromy.Structure.realizable_of_partrec`.
--
--   Statement elaboration dependencies: `Monodromy.Structure.ProbeFreeRealizable`, `Monodromy.Structure.Realizable`.
--
--   Proof elaboration dependencies: `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.ProbeFree`, `Monodromy.ForwardBoundary.hardFunction`, `Monodromy.ForwardBoundary.hardFunction_partrec`, `Monodromy.Structure.Computes`, `Monodromy.Structure.ProbeFreeRealizable`, `Monodromy.Structure.Realizable`, `Monodromy.Structure.no_probeFree_hardFunction`, `Monodromy.Structure.realizable_of_partrec`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Structure.lean (file SHA-256 cdcfb6852947e60cdaf4cef38f43a83b8651973b4e92feec928b6408b60b877e):
--   Monodromy.Structure.conditional_gates_strictly_extend at L107-L113 [UTF-8 4968:5410].

module
public import Definitions.Def_Monodromy_Structure
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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Computability.Halting
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Set.Finite.Basic
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
open Monodromy.Structure
open CoupledContinuation NativeInterface

theorem Monodromy.Structure.conditional_gates_strictly_extend :
    ∃ function : ℕ → Part ℕ, Realizable function ∧ ¬ ProbeFreeRealizable function := by sorry
