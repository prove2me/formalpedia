-- Prove2me | Theorems.Thm_Monodromy_Structure_analytic_computes_iff
-- name    : Monodromy.Structure.analytic_computes_iff
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:44:28.001241+00:00
-- url     : https://prove2.me/theorems/095e2c2c-7dbc-40d9-82db-e9f46bb50658
-- title:
--   The Direct Analytic Comparator Has Exactly the Native Numeric Graph
-- statement:
--   For every positive natural degree d, program P:Program d and partial function f:ℕ→Part ℕ, the following are equivalent: for every n,v∈ℕ, v belongs to f(n) exactly when some integer label triple λ is a complete result of the direct comparator from the real embedding of inputLabels(n), with outputLabels(λ)=v; and P computes f by the native fixed-interface graph predicate. The comparator result in the first condition is the real embedding of λ. No effectiveness assumption on f or agreement from noninteger initial states is asserted.
--
--   Statement dependencies: `Monodromy.AnalyticComparison.State`, `Monodromy.AnalyticComparison.embed`, `Monodromy.AnalyticComparison.eval`, `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Program`, `Monodromy.NativeInterface.inputLabels`, `Monodromy.NativeInterface.outputLabels`, `Monodromy.Structure.Computes`.
--
--   Original proof dependencies: `Monodromy.AnalyticComparison.State`, `Monodromy.AnalyticComparison.embed`, `Monodromy.AnalyticComparison.eval`, `Monodromy.AnalyticComparison.result_iff`, `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Labels.prepare`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.NativeInterface.inputLabels`, `Monodromy.NativeInterface.outputLabels`, `Monodromy.Structure.Computes`.
--
--   Statement elaboration dependencies: `Monodromy.AnalyticComparison.State`, `Monodromy.AnalyticComparison.embed`, `Monodromy.AnalyticComparison.eval`, `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Program`, `Monodromy.NativeInterface.inputLabels`, `Monodromy.NativeInterface.outputLabels`, `Monodromy.Structure.Computes`.
--
--   Proof elaboration dependencies: `Monodromy.AnalyticComparison.State`, `Monodromy.AnalyticComparison.embed`, `Monodromy.AnalyticComparison.eval`, `Monodromy.AnalyticComparison.result_iff`, `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Labels.prepare`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.NativeInterface.inputLabels`, `Monodromy.NativeInterface.outputLabels`, `Monodromy.Structure.Computes`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Structure.lean (file SHA-256 cdcfb6852947e60cdaf4cef38f43a83b8651973b4e92feec928b6408b60b877e):
--   Monodromy.Structure.analytic_computes_iff at L121-L129 [UTF-8 5510:6049].

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

theorem Monodromy.Structure.analytic_computes_iff {degree : ℕ} [NeZero degree]
    (program : Program degree) (function : ℕ → Part ℕ) :
    (∀ input value, value ∈ function input ↔ ∃ labels : Labels,
      AnalyticComparison.embed labels ∈ AnalyticComparison.eval program
        (AnalyticComparison.embed (inputLabels input)) ∧ outputLabels labels = value) ↔
      Computes program function := by sorry
