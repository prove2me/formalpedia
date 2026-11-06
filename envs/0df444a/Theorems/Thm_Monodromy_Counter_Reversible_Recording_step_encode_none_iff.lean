-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_Recording_step_encode_none_iff
-- name    : Monodromy.Counter.Reversible.Recording.step_encode_none_iff
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:40:48.10359+00:00
-- url     : https://prove2.me/theorems/94453de2-bdde-4f63-9a66-995c69785d55
-- title:
--   Recording preserves absence of the source step
-- statement:
--   For arbitrary natural n,m, every n-counter program P, source configuration s and natural history h, the reversible recording table has no optional step from encode(s,h) if and only if P has no optional step from s. The encoding retains the source counters, history and zero workspace at the corresponding recording dispatch.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.encode`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.table`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.step`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Action`, `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.entry`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Recording.Active`, `Monodromy.Counter.Reversible.Recording.Arc`, `Monodromy.Counter.Reversible.Recording.Extra`, `Monodromy.Counter.Reversible.Recording.Node`, `Monodromy.Counter.Reversible.Recording.arcEdge`, `Monodromy.Counter.Reversible.Recording.arcEquiv`, `Monodromy.Counter.Reversible.Recording.base`, `Monodromy.Counter.Reversible.Recording.dispatch`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.encode`, `Monodromy.Counter.Reversible.Recording.extraEdge`, `Monodromy.Counter.Reversible.Recording.extraOperation`, `Monodromy.Counter.Reversible.Recording.extraOperation_dec`, `Monodromy.Counter.Reversible.Recording.extraOperation_inc`, `Monodromy.Counter.Reversible.Recording.extraOrigin`, `Monodromy.Counter.Reversible.Recording.extraOrigin_dec`, `Monodromy.Counter.Reversible.Recording.extraOrigin_inc`, `Monodromy.Counter.Reversible.Recording.frame`, `Monodromy.Counter.Reversible.Recording.frame_old`, `Monodromy.Counter.Reversible.Recording.halt_no_outgoing`, `Monodromy.Counter.Reversible.Recording.nodeEquiv`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.table`, `Monodromy.Counter.Reversible.Recording.table_arc`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.Reversible.step_none_iff`, `Monodromy.Counter.step`, `Monodromy.Counter.step_halt`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.encode`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.table`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.step`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Action`, `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Radix.edges`, `Monodromy.Counter.Reversible.Radix.entry`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Recording.Active`, `Monodromy.Counter.Reversible.Recording.Arc`, `Monodromy.Counter.Reversible.Recording.Extra`, `Monodromy.Counter.Reversible.Recording.Node`, `Monodromy.Counter.Reversible.Recording.arcEdge`, `Monodromy.Counter.Reversible.Recording.arcEquiv`, `Monodromy.Counter.Reversible.Recording.base`, `Monodromy.Counter.Reversible.Recording.dispatch`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.encode`, `Monodromy.Counter.Reversible.Recording.extraEdge`, `Monodromy.Counter.Reversible.Recording.extraOperation`, `Monodromy.Counter.Reversible.Recording.extraOperation_dec`, `Monodromy.Counter.Reversible.Recording.extraOperation_inc`, `Monodromy.Counter.Reversible.Recording.extraOrigin`, `Monodromy.Counter.Reversible.Recording.extraOrigin_dec`, `Monodromy.Counter.Reversible.Recording.extraOrigin_inc`, `Monodromy.Counter.Reversible.Recording.frame`, `Monodromy.Counter.Reversible.Recording.frame_old`, `Monodromy.Counter.Reversible.Recording.framed`, `Monodromy.Counter.Reversible.Recording.halt_no_outgoing`, `Monodromy.Counter.Reversible.Recording.nodeEquiv`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.table`, `Monodromy.Counter.Reversible.Recording.table_arc`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.Reversible.step_none_iff`, `Monodromy.Counter.step`, `Monodromy.Counter.step_halt`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.Recording.step_encode_none_iff at L5978-L6019 [UTF-8 298107:300458].

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

theorem Monodromy.Counter.Reversible.Recording.step_encode_none_iff (program : Counter.Program n m)
    (state : Counter.Configuration n m) (history : ℕ) :
    step (table program) (encode state history) = none ↔ Counter.step program state = none := by sorry
