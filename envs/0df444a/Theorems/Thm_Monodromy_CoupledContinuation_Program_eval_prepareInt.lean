-- Prove2me | Theorems.Thm_Monodromy_CoupledContinuation_Program_eval_prepareInt
-- name    : Monodromy.CoupledContinuation.Program.eval_prepareInt
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:35:18.159359+00:00
-- url     : https://prove2.me/theorems/6bfb94ec-c2f5-4782-8ccc-59624c601c70
-- title:
--   Native Partial Evaluation Equals Prepared Integer Evaluation
-- statement:
--   For every positive natural degree d, every finite word-and-stop program P of degree d, and every integer label triple λ∈ℤ³, $P.\operatorname{eval}(\operatorname{prepare}(\lambda))=\operatorname{map}(\operatorname{prepare})(P.\operatorname{evalInt}(\lambda))$. This is equality of partial complete-state results, including undefinedness, rather than only equality of one-step transitions.
--
--   Statement dependencies: `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Labels.prepare`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.CoupledContinuation.Program.evalInt`.
--
--   Original proof dependencies: `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Labels.prepare`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.CoupledContinuation.Program.stepInt`, `Monodromy.CoupledContinuation.Program.step_prepareInt`.
--
--   Statement elaboration dependencies: `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Labels.prepare`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.CoupledContinuation.Program.evalInt`.
--
--   Proof elaboration dependencies: `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Labels.prepare`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.CoupledContinuation.Program.stepInt`, `Monodromy.CoupledContinuation.Program.step_prepareInt`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Continuation.lean (file SHA-256 c41996cad30503403fe284de8929124f849aa5fd0aaba5433e5e0d4d36fec912):
--   Monodromy.CoupledContinuation.Program.eval_prepareInt at L2379-L2393 [UTF-8 119780:120578].

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
open Monodromy
open Monodromy.CoupledContinuation
open Monodromy.CoupledContinuation.Program
variable {degree : ℕ} [NeZero degree]

theorem Monodromy.CoupledContinuation.Program.eval_prepareInt (program : Program degree) (labels : Labels) :
    program.eval (Labels.prepare labels) = Labels.prepare <$> program.evalInt labels := by sorry
