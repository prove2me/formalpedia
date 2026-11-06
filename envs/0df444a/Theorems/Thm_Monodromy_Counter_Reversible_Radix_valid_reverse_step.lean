-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_Radix_valid_reverse_step
-- name    : Monodromy.Counter.Reversible.Radix.valid_reverse_step
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:40:32.632228+00:00
-- url     : https://prove2.me/theorems/ce058fd3-40ec-4178-9e91-9ed2e91b4811
-- title:
--   Reversing a radix edge preserves the port invariant
-- statement:
--   For every positive radix p and any two integer-counter states s,t, if s satisfies the radix table’s Valid invariant and the reversed table takes a successful step s→t, then t also satisfies Valid. This invariant requires both registers to be nonnegative and the zero, positive or nonzero conditions specified by the current global or remainder-phase control port.
--
--   Statement dependencies: `Monodromy.Counter.Reversible.Radix.Valid`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Radix.table`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.reverseTable`, `Monodromy.Counter.Reversible.step`.
--
--   Original proof dependencies: `Monodromy.Counter.Reversible.Action`, `Monodromy.Counter.Reversible.Action.apply`, `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.Radix.Arc`, `Monodromy.Counter.Reversible.Radix.Node`, `Monodromy.Counter.Reversible.Radix.Valid`, `Monodromy.Counter.Reversible.Radix.admissible`, `Monodromy.Counter.Reversible.Radix.arcEquiv`, `Monodromy.Counter.Reversible.Radix.destination`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.next`, `Monodromy.Counter.Reversible.Radix.nodeEquiv`, `Monodromy.Counter.Reversible.Radix.operation`, `Monodromy.Counter.Reversible.Radix.origin`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Radix.table`, `Monodromy.Counter.Reversible.Radix.table_arc`, `Monodromy.Counter.Reversible.Radix.targetCompatible`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.StepRel`, `Monodromy.Counter.Reversible.reverseAction`, `Monodromy.Counter.Reversible.reverseTable`, `Monodromy.Counter.Reversible.reverseTable_deterministic`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.Reversible.step_iff`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Reversible.Radix.Valid`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Radix.table`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.reverseTable`, `Monodromy.Counter.Reversible.step`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Reversible.Action`, `Monodromy.Counter.Reversible.Action.apply`, `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.Radix.Arc`, `Monodromy.Counter.Reversible.Radix.Node`, `Monodromy.Counter.Reversible.Radix.Valid`, `Monodromy.Counter.Reversible.Radix.admissible`, `Monodromy.Counter.Reversible.Radix.arcEquiv`, `Monodromy.Counter.Reversible.Radix.destination`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.next`, `Monodromy.Counter.Reversible.Radix.nodeEquiv`, `Monodromy.Counter.Reversible.Radix.operation`, `Monodromy.Counter.Reversible.Radix.origin`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Radix.table`, `Monodromy.Counter.Reversible.Radix.table_arc`, `Monodromy.Counter.Reversible.Radix.targetCompatible`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.StepRel`, `Monodromy.Counter.Reversible.reverseAction`, `Monodromy.Counter.Reversible.reverseEdge`, `Monodromy.Counter.Reversible.reverseTable`, `Monodromy.Counter.Reversible.reverseTable_deterministic`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.Reversible.step_iff`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.Radix.valid_reverse_step at L4676-L4693 [UTF-8 231257:232336].

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
open Monodromy.Counter.Reversible.Radix
variable (p : ℕ) [NeZero p]

theorem Monodromy.Counter.Reversible.Radix.valid_reverse_step {first last : State 2 (size p)}
    (valid : Valid p first) (transition : step (reverseTable (table p)) first = some last) :
    Valid p last := by sorry
