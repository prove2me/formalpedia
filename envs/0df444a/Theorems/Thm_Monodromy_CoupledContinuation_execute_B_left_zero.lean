-- Prove2me | Theorems.Thm_Monodromy_CoupledContinuation_execute_B_left_zero
-- name    : Monodromy.CoupledContinuation.execute_B_left_zero
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:36:11.596257+00:00
-- url     : https://prove2.me/theorems/9afeafda-cad3-4eab-bee5-d22b208e5e73
-- title:
--   A Left Root Equal to One Produces One Control Period
-- statement:
--   For every state s in the coupled three-coordinate fiber, if its retained left lower root equals 1, then the upper coordinate after actual execution of the fixed left conditional driver B_left is the original upper coordinate plus $2\pi i$. The hypothesis concerns the complex root itself; the other memory root and the original upper coordinate are unrestricted.
--
--   Statement dependencies: `Monodromy.CoupledContinuation.B_left`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Punctured`, `Monodromy.CoupledContinuation.execute`, `Monodromy.NestedContinuation.period`.
--
--   Original proof dependencies: `Monodromy.CoupledContinuation.B_left`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Punctured`, `Monodromy.CoupledContinuation.execute`, `Monodromy.CoupledContinuation.execute_B_left`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.CoupledContinuation.prepare_surjective`, `Monodromy.CoupledContinuation.upperRoot`, `Monodromy.NestedContinuation.firstRoot`, `Monodromy.NestedContinuation.firstRoot_injective`, `Monodromy.NestedContinuation.period`.
--
--   Statement elaboration dependencies: `Monodromy.CoupledContinuation.B_left`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Punctured`, `Monodromy.CoupledContinuation.execute`, `Monodromy.NestedContinuation.period`.
--
--   Proof elaboration dependencies: `Monodromy.CoupledContinuation.B_left`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Punctured`, `Monodromy.CoupledContinuation.execute`, `Monodromy.CoupledContinuation.execute_B_left`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.CoupledContinuation.prepare_surjective`, `Monodromy.CoupledContinuation.upperRoot`, `Monodromy.NestedContinuation.firstRoot`, `Monodromy.NestedContinuation.firstRoot_injective`, `Monodromy.NestedContinuation.period`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Continuation.lean (file SHA-256 c41996cad30503403fe284de8929124f849aa5fd0aaba5433e5e0d4d36fec912):
--   Monodromy.CoupledContinuation.execute_B_left_zero at L813-L826 [UTF-8 39656:40461].

module
public import Definitions.Def_Monodromy_Continuation
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
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Monodromy
open Monodromy.CoupledContinuation

theorem Monodromy.CoupledContinuation.execute_B_left_zero (state : Memory) (zero : state.val.1.1.val = 1) :
    (execute B_left state).val.2 = state.val.2 + NestedContinuation.period 1 := by sorry
