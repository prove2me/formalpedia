-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_Recording_packing_internal_reaches
-- name    : Monodromy.Counter.Reversible.Recording.packing_internal_reaches
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:49:21.135627+00:00
-- url     : https://prove2.me/theorems/98d04db9-949b-48db-bb5a-02d255ef6750
-- title:
--   The copied history packer avoids earlier dispatches
-- statement:
--   For any natural n,m, n-counter program P, row r, digit s<2m+1, natural source-register vector v and history h, the recording table has an internal finite run from port(r,s) with registers (v,h,0) to dispatch(r) with registers (v,(2m+1)h+s,0). Each departure state in the run avoids every recording dispatch; s=0 is allowed, and no strict history-growth conclusion is asserted.
--
--   Statement dependencies: `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Recording.InternalReaches`, `Monodromy.Counter.Reversible.Recording.base`, `Monodromy.Counter.Reversible.Recording.dispatch`, `Monodromy.Counter.Reversible.Recording.framed`, `Monodromy.Counter.Reversible.Recording.port`.
--
--   Original proof dependencies: `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Glue.mapEdge`, `Monodromy.Counter.Reversible.Glue.mapState`, `Monodromy.Counter.Reversible.Glue.step_map_live`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.entry`, `Monodromy.Counter.Reversible.Radix.finish`, `Monodromy.Counter.Reversible.Radix.point`, `Monodromy.Counter.Reversible.Radix.reverse_pack`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Radix.table`, `Monodromy.Counter.Reversible.Radix.targetCompatible`, `Monodromy.Counter.Reversible.Recording.Arc`, `Monodromy.Counter.Reversible.Recording.Boundary`, `Monodromy.Counter.Reversible.Recording.Extra`, `Monodromy.Counter.Reversible.Recording.InternalReaches`, `Monodromy.Counter.Reversible.Recording.InternalStep`, `Monodromy.Counter.Reversible.Recording.arcEquiv`, `Monodromy.Counter.Reversible.Recording.base`, `Monodromy.Counter.Reversible.Recording.base_nonzero`, `Monodromy.Counter.Reversible.Recording.copy`, `Monodromy.Counter.Reversible.Recording.deterministic`, `Monodromy.Counter.Reversible.Recording.dispatch`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.frame`, `Monodromy.Counter.Reversible.Recording.frame_extend`, `Monodromy.Counter.Reversible.Recording.framed`, `Monodromy.Counter.Reversible.Recording.historyRegister`, `Monodromy.Counter.Reversible.Recording.historyRegister_injective`, `Monodromy.Counter.Reversible.Recording.local_step_not_entry`, `Monodromy.Counter.Reversible.Recording.not_boundary_copy`, `Monodromy.Counter.Reversible.Recording.packing`, `Monodromy.Counter.Reversible.Recording.packing_deterministic`, `Monodromy.Counter.Reversible.Recording.port`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.table`, `Monodromy.Counter.Reversible.Recording.table_arc`, `Monodromy.Counter.Reversible.RegisterRelocation.embed`, `Monodromy.Counter.Reversible.RegisterRelocation.mapTable`, `Monodromy.Counter.Reversible.RegisterRelocation.step_embed`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.reverseTable`, `Monodromy.Counter.Reversible.reverseTable_deterministic`, `Monodromy.Counter.Reversible.step`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Recording.InternalReaches`, `Monodromy.Counter.Reversible.Recording.base`, `Monodromy.Counter.Reversible.Recording.dispatch`, `Monodromy.Counter.Reversible.Recording.framed`, `Monodromy.Counter.Reversible.Recording.port`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Glue.mapEdge`, `Monodromy.Counter.Reversible.Glue.mapState`, `Monodromy.Counter.Reversible.Glue.step_map_live`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.entry`, `Monodromy.Counter.Reversible.Radix.finish`, `Monodromy.Counter.Reversible.Radix.point`, `Monodromy.Counter.Reversible.Radix.reverse_pack`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Radix.table`, `Monodromy.Counter.Reversible.Radix.targetCompatible`, `Monodromy.Counter.Reversible.Recording.Arc`, `Monodromy.Counter.Reversible.Recording.Boundary`, `Monodromy.Counter.Reversible.Recording.Extra`, `Monodromy.Counter.Reversible.Recording.InternalReaches`, `Monodromy.Counter.Reversible.Recording.InternalStep`, `Monodromy.Counter.Reversible.Recording.arcEdge`, `Monodromy.Counter.Reversible.Recording.arcEquiv`, `Monodromy.Counter.Reversible.Recording.base`, `Monodromy.Counter.Reversible.Recording.base_nonzero`, `Monodromy.Counter.Reversible.Recording.copy`, `Monodromy.Counter.Reversible.Recording.deterministic`, `Monodromy.Counter.Reversible.Recording.dispatch`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.frame`, `Monodromy.Counter.Reversible.Recording.frame_extend`, `Monodromy.Counter.Reversible.Recording.framed`, `Monodromy.Counter.Reversible.Recording.historyRegister`, `Monodromy.Counter.Reversible.Recording.historyRegister_injective`, `Monodromy.Counter.Reversible.Recording.local_step_not_entry`, `Monodromy.Counter.Reversible.Recording.not_boundary_copy`, `Monodromy.Counter.Reversible.Recording.packing`, `Monodromy.Counter.Reversible.Recording.packing_deterministic`, `Monodromy.Counter.Reversible.Recording.port`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.table`, `Monodromy.Counter.Reversible.Recording.table_arc`, `Monodromy.Counter.Reversible.RegisterRelocation.embed`, `Monodromy.Counter.Reversible.RegisterRelocation.mapTable`, `Monodromy.Counter.Reversible.RegisterRelocation.step_embed`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.reverseTable`, `Monodromy.Counter.Reversible.reverseTable_deterministic`, `Monodromy.Counter.Reversible.step`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.Recording.packing_internal_reaches at L6311-L6343 [UTF-8 315523:317704].

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

theorem Monodromy.Counter.Reversible.Recording.packing_internal_reaches (program : Counter.Program n m)
    (row : Fin m) (symbol : Fin (base m)) (values : Fin n → ℕ) (history : ℕ) :
    InternalReaches program
      (framed (port row symbol) values history 0)
      (framed (dispatch row) values (base m * history + symbol.val : ℕ) 0) := by sorry
