-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_Recording_halt_no_outgoing
-- name    : Monodromy.Counter.Reversible.Recording.halt_no_outgoing
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:30:13.038472+00:00
-- url     : https://prove2.me/theorems/ce4d9d1d-c835-4b4b-8993-c5edaffd15ca
-- title:
--   A halted source row has no outgoing recording edge
-- statement:
--   For every natural n,m, n-counter program P, control row r with P(r)=halt, and edge index j of its reversible recording table, edge j does not have source equal to dispatch(r). The exclusion concerns all table edges, independently of register values.
--
--   Statement dependencies: `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Recording.dispatch`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.table`.
--
--   Original proof dependencies: `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.entry`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Recording.Active`, `Monodromy.Counter.Reversible.Recording.Arc`, `Monodromy.Counter.Reversible.Recording.Extra`, `Monodromy.Counter.Reversible.Recording.Node`, `Monodromy.Counter.Reversible.Recording.arcEdge`, `Monodromy.Counter.Reversible.Recording.arcEquiv`, `Monodromy.Counter.Reversible.Recording.base`, `Monodromy.Counter.Reversible.Recording.copy`, `Monodromy.Counter.Reversible.Recording.copy_eq_iff`, `Monodromy.Counter.Reversible.Recording.dispatch`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.extraOrigin`, `Monodromy.Counter.Reversible.Recording.extraOrigin_dec`, `Monodromy.Counter.Reversible.Recording.extraOrigin_inc`, `Monodromy.Counter.Reversible.Recording.nodeEquiv`, `Monodromy.Counter.Reversible.Recording.packing`, `Monodromy.Counter.Reversible.Recording.packing_no_outgoing_dispatch`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.table`, `Monodromy.Counter.Reversible.Recording.table_arc`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Recording.dispatch`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.table`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.entry`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Recording.Active`, `Monodromy.Counter.Reversible.Recording.Arc`, `Monodromy.Counter.Reversible.Recording.Extra`, `Monodromy.Counter.Reversible.Recording.Node`, `Monodromy.Counter.Reversible.Recording.arcEdge`, `Monodromy.Counter.Reversible.Recording.arcEquiv`, `Monodromy.Counter.Reversible.Recording.base`, `Monodromy.Counter.Reversible.Recording.copy`, `Monodromy.Counter.Reversible.Recording.copy_eq_iff`, `Monodromy.Counter.Reversible.Recording.dispatch`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.extraOrigin`, `Monodromy.Counter.Reversible.Recording.extraOrigin_dec`, `Monodromy.Counter.Reversible.Recording.extraOrigin_inc`, `Monodromy.Counter.Reversible.Recording.nodeEquiv`, `Monodromy.Counter.Reversible.Recording.packing`, `Monodromy.Counter.Reversible.Recording.packing_no_outgoing_dispatch`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.table`, `Monodromy.Counter.Reversible.Recording.table_arc`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.Recording.halt_no_outgoing at L5948-L5976 [UTF-8 296613:298105].

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

theorem Monodromy.Counter.Reversible.Recording.halt_no_outgoing (program : Counter.Program n m) (row : Fin m)
    (halted : program row = .halt) (index : Fin (edges program)) :
    (table program index).source ≠ dispatch row := by sorry
