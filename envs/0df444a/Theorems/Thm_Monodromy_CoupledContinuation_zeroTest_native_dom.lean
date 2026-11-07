-- Prove2me | Theorems.Thm_Monodromy_CoupledContinuation_zeroTest_native_dom
-- name    : Monodromy.CoupledContinuation.zeroTest_native_dom
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:42:42.167094+00:00
-- url     : https://prove2.me/theorems/e9d07c65-b2cf-4881-a0b4-b5d83e0a98f9
-- title:
--   The Native Zero-Test Program Terminates Exactly on Integer Zero
-- statement:
--   For every integer n, the specified native zeroTest program has a defined partial evaluation from prepare(n,0,0) if and only if n=0. This is a termination-domain statement for actual geometric execution, with no output-value claim.
--
--   Statement dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.CoupledContinuation.zeroTest`.
--
--   Original proof dependencies: `Monodromy.CoupledContinuation.Gate`, `Monodromy.CoupledContinuation.Gate.evalInt`, `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Labels.prepare`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.CoupledContinuation.Program.evalInt`, `Monodromy.CoupledContinuation.Program.eval_prepareInt`, `Monodromy.CoupledContinuation.Program.haltInt`, `Monodromy.CoupledContinuation.Program.indexInt`, `Monodromy.CoupledContinuation.Program.nextInt`, `Monodromy.CoupledContinuation.Word`, `Monodromy.CoupledContinuation.Word.atom`, `Monodromy.CoupledContinuation.Word.evalInt`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.CoupledContinuation.zeroTest`, `Monodromy.Observation.stopped`, `Monodromy.Observation.stopped_dom_iff`.
--
--   Statement elaboration dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.CoupledContinuation.zeroTest`.
--
--   Proof elaboration dependencies: `Monodromy.CoupledContinuation.Gate`, `Monodromy.CoupledContinuation.Gate.evalInt`, `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Labels.prepare`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.CoupledContinuation.Program.evalInt`, `Monodromy.CoupledContinuation.Program.eval_prepareInt`, `Monodromy.CoupledContinuation.Program.haltInt`, `Monodromy.CoupledContinuation.Program.indexInt`, `Monodromy.CoupledContinuation.Program.nextInt`, `Monodromy.CoupledContinuation.Word`, `Monodromy.CoupledContinuation.Word.atom`, `Monodromy.CoupledContinuation.Word.evalInt`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.CoupledContinuation.zeroTest`, `Monodromy.Observation.stopped`, `Monodromy.Observation.stopped_dom_iff`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/ForwardBoundary.lean (file SHA-256 79994010f524b607d5f4d56631e4490998ab2e44fa455569a55df12bc89c47b2):
--   Monodromy.CoupledContinuation.zeroTest_native_dom at L199-L223 [UTF-8 9849:11091].

module
public import Definitions.Def_Monodromy_ForwardBoundary
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
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Set.Finite.Basic
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

theorem Monodromy.CoupledContinuation.zeroTest_native_dom (input : ℤ) :
    (zeroTest.eval (prepare input 0 0)).Dom ↔ input = 0 := by sorry
