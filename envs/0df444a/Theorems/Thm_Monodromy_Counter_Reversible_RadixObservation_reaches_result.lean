-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_RadixObservation_reaches_result
-- name    : Monodromy.Counter.Reversible.RadixObservation.reaches_result
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:49:05.659875+00:00
-- url     : https://prove2.me/theorems/6f29b30d-7f8a-45a4-9aad-674080bc69f0
-- title:
--   A remainder-indexed permutation preserves the input counters
-- statement:
--   For every positive p, arbitrary natural m, family of permutations πᵣ of Fin m indexed by r<p, row i∈Fin m and natural value x, the reversible observation table has a finite run from its input port i with counters (x,0) to its output port π₍ₓ mod p₎(i) with the same counters (x,0). The observation changes only the selected finite output row.
--
--   Statement dependencies: `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.Reversible.RadixObservation.edges`, `Monodromy.Counter.Reversible.RadixObservation.inputPort`, `Monodromy.Counter.Reversible.RadixObservation.outputPort`, `Monodromy.Counter.Reversible.RadixObservation.point`, `Monodromy.Counter.Reversible.RadixObservation.size`, `Monodromy.Counter.Reversible.RadixObservation.table`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`.
--
--   Original proof dependencies: `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.Reversible.Glue.mapState`, `Monodromy.Counter.Reversible.Glue.reaches_map_live`, `Monodromy.Counter.Reversible.Radix.deterministic`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.entry`, `Monodromy.Counter.Reversible.Radix.finish`, `Monodromy.Counter.Reversible.Radix.point`, `Monodromy.Counter.Reversible.Radix.reaches_result`, `Monodromy.Counter.Reversible.Radix.reverse_pack`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Radix.table`, `Monodromy.Counter.Reversible.Radix.targetCompatible`, `Monodromy.Counter.Reversible.RadixObservation.RawArc`, `Monodromy.Counter.Reversible.RadixObservation.arcEquiv`, `Monodromy.Counter.Reversible.RadixObservation.back`, `Monodromy.Counter.Reversible.RadixObservation.deterministic`, `Monodromy.Counter.Reversible.RadixObservation.edges`, `Monodromy.Counter.Reversible.RadixObservation.front`, `Monodromy.Counter.Reversible.RadixObservation.front_finish`, `Monodromy.Counter.Reversible.RadixObservation.inputPort`, `Monodromy.Counter.Reversible.RadixObservation.outputPort`, `Monodromy.Counter.Reversible.RadixObservation.point`, `Monodromy.Counter.Reversible.RadixObservation.size`, `Monodromy.Counter.Reversible.RadixObservation.table`, `Monodromy.Counter.Reversible.RadixObservation.table_back`, `Monodromy.Counter.Reversible.RadixObservation.table_front`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.reverseTable`, `Monodromy.Counter.Reversible.reverseTable_deterministic`, `Monodromy.Counter.Reversible.step`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.Reversible.RadixObservation.edges`, `Monodromy.Counter.Reversible.RadixObservation.inputPort`, `Monodromy.Counter.Reversible.RadixObservation.outputPort`, `Monodromy.Counter.Reversible.RadixObservation.point`, `Monodromy.Counter.Reversible.RadixObservation.size`, `Monodromy.Counter.Reversible.RadixObservation.table`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.Reversible.Glue.mapState`, `Monodromy.Counter.Reversible.Glue.reaches_map_live`, `Monodromy.Counter.Reversible.Radix.deterministic`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.entry`, `Monodromy.Counter.Reversible.Radix.finish`, `Monodromy.Counter.Reversible.Radix.point`, `Monodromy.Counter.Reversible.Radix.reaches_result`, `Monodromy.Counter.Reversible.Radix.reverse_pack`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Radix.table`, `Monodromy.Counter.Reversible.Radix.targetCompatible`, `Monodromy.Counter.Reversible.RadixObservation.RawArc`, `Monodromy.Counter.Reversible.RadixObservation.arcEquiv`, `Monodromy.Counter.Reversible.RadixObservation.back`, `Monodromy.Counter.Reversible.RadixObservation.deterministic`, `Monodromy.Counter.Reversible.RadixObservation.edges`, `Monodromy.Counter.Reversible.RadixObservation.front`, `Monodromy.Counter.Reversible.RadixObservation.front_finish`, `Monodromy.Counter.Reversible.RadixObservation.inputPort`, `Monodromy.Counter.Reversible.RadixObservation.outputPort`, `Monodromy.Counter.Reversible.RadixObservation.point`, `Monodromy.Counter.Reversible.RadixObservation.size`, `Monodromy.Counter.Reversible.RadixObservation.table`, `Monodromy.Counter.Reversible.RadixObservation.table_back`, `Monodromy.Counter.Reversible.RadixObservation.table_front`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.reverseTable`, `Monodromy.Counter.Reversible.reverseTable_deterministic`, `Monodromy.Counter.Reversible.step`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.RadixObservation.reaches_result at L5240-L5268 [UTF-8 262225:264431].

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
open Monodromy.Counter.Reversible.RadixObservation
variable (p m : ℕ) [NeZero p]

theorem Monodromy.Counter.Reversible.RadixObservation.reaches_result (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m) (value : ℕ) :
    StateTransition.Reaches (step (table p m permutation))
      (point p m permutation (inputPort p m permutation row) value 0)
      (point p m permutation (outputPort p m permutation (permutation (Counter.DivMod.residue p value) row)) value 0) := by sorry
