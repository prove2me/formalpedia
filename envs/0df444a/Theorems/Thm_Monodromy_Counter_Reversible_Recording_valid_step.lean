-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_Recording_valid_step
-- name    : Monodromy.Counter.Reversible.Recording.valid_step
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:45:38.481131+00:00
-- url     : https://prove2.me/theorems/20474266-cc49-439a-9eac-727c84d4e3c9
-- title:
--   Every recording step preserves its natural-domain invariant
-- statement:
--   For arbitrary natural n,m and source n-counter program P, every successful step of its reversible recording table from a Valid state reaches another Valid state. Valid requires nonnegative original registers and the history/workspace radix conditions at copied ports; at decrement middle ports it requires nonnegative history, zero workspace and positivity of the register awaiting decrement.
--
--   Statement dependencies: `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Recording.Valid`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.table`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`.
--
--   Original proof dependencies: `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Action`, `Monodromy.Counter.Reversible.Action.apply`, `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Recording.Arc`, `Monodromy.Counter.Reversible.Recording.Extra`, `Monodromy.Counter.Reversible.Recording.Valid`, `Monodromy.Counter.Reversible.Recording.arcEdge`, `Monodromy.Counter.Reversible.Recording.arcEquiv`, `Monodromy.Counter.Reversible.Recording.base`, `Monodromy.Counter.Reversible.Recording.deterministic`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.extra_valid_edge`, `Monodromy.Counter.Reversible.Recording.packing_valid_edge`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.table`, `Monodromy.Counter.Reversible.Recording.table_arc`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.StepRel`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.Reversible.step_iff`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Recording.Valid`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.table`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Action`, `Monodromy.Counter.Reversible.Action.apply`, `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Recording.Arc`, `Monodromy.Counter.Reversible.Recording.Extra`, `Monodromy.Counter.Reversible.Recording.Valid`, `Monodromy.Counter.Reversible.Recording.arcEdge`, `Monodromy.Counter.Reversible.Recording.arcEquiv`, `Monodromy.Counter.Reversible.Recording.base`, `Monodromy.Counter.Reversible.Recording.deterministic`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.extra_valid_edge`, `Monodromy.Counter.Reversible.Recording.packing_valid_edge`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.table`, `Monodromy.Counter.Reversible.Recording.table_arc`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.StepRel`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.Reversible.step_iff`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.Recording.valid_step at L6237-L6253 [UTF-8 311657:312641].

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
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Recording
variable {n m : ℕ}

theorem Monodromy.Counter.Reversible.Recording.valid_step (program : Counter.Program n m) {first last : State (n + 2) (size m)}
    (valid : Valid program first) (transition : step (table program) first = some last) :
    Valid program last := by sorry
