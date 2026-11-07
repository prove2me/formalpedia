-- Prove2me | Theorems.Thm_Monodromy_Structure_continuation_characterization
-- name    : Monodromy.Structure.continuation_characterization
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:50:39.015306+00:00
-- url     : https://prove2.me/theorems/3e7e86f2-5aeb-4b79-8683-af79a9c668cb
-- title:
--   The Full Native Program Language Computes Exactly the Partial Recursive Functions
-- statement:
--   For every partial function f:ℕ→Part ℕ, there exists a finite native Program of some positive cover degree whose complete execution realizes f under the fixed inputLabels preparation and outputLabels readout if and only if f is partial recursive. Realization uses equality of the full numeric result graph for every natural input and output value. The quantified programs are the entire Program language, rather than only the reversible compiler image.
--
--   Statement dependencies: `Monodromy.Structure.Realizable`.
--
--   Original proof dependencies: `Monodromy.Structure.Realizable`, `Monodromy.Structure.partrec_of_realizable`, `Monodromy.Structure.realizable_of_partrec`.
--
--   Statement elaboration dependencies: `Monodromy.Structure.Realizable`.
--
--   Proof elaboration dependencies: `Monodromy.Structure.Realizable`, `Monodromy.Structure.partrec_of_realizable`, `Monodromy.Structure.realizable_of_partrec`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Structure.lean (file SHA-256 cdcfb6852947e60cdaf4cef38f43a83b8651973b4e92feec928b6408b60b877e):
--   Monodromy.Structure.continuation_characterization at L82-L85 [UTF-8 3673:3933].

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

theorem Monodromy.Structure.continuation_characterization (function : ℕ → Part ℕ) :
    Realizable function ↔ Partrec function := by sorry
