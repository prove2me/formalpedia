-- Prove2me | Theorems.Thm_Monodromy_AnalyticComparison_eval_embed
-- name    : Monodromy.AnalyticComparison.eval_embed
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:26:23.21549+00:00
-- url     : https://prove2.me/theorems/3ece95ab-f5f9-4f66-91ec-4553acd3eba4
-- title:
--   Direct Analytic Evaluation Preserves Embedded Integer Results
-- statement:
--   For every positive natural degree d, every program P:Program d and every integer label triple λ, the direct three-real-coordinate comparator’s partial evaluation from the coordinatewise real embedding of λ equals the real embedding mapped over P.evalInt(λ). Equality includes complete results and undefinedness; the initial states quantified here are embedded integer triples.
--
--   Statement dependencies: `Monodromy.AnalyticComparison.State`, `Monodromy.AnalyticComparison.embed`, `Monodromy.AnalyticComparison.eval`, `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.evalInt`.
--
--   Original proof dependencies: `Monodromy.AnalyticComparison.State`, `Monodromy.AnalyticComparison.embed`, `Monodromy.AnalyticComparison.step`, `Monodromy.AnalyticComparison.step_embed`, `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.stepInt`.
--
--   Statement elaboration dependencies: `Monodromy.AnalyticComparison.State`, `Monodromy.AnalyticComparison.embed`, `Monodromy.AnalyticComparison.eval`, `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.evalInt`.
--
--   Proof elaboration dependencies: `Monodromy.AnalyticComparison.State`, `Monodromy.AnalyticComparison.embed`, `Monodromy.AnalyticComparison.step`, `Monodromy.AnalyticComparison.step_embed`, `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.stepInt`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Effectiveness.lean (file SHA-256 90d9fd8cedd8839d63110e1673758c66fd34eb170016cb9a2ad4c136d0777dd3):
--   Monodromy.AnalyticComparison.eval_embed at L580-L594 [UTF-8 27331:28088].

module
public import Definitions.Def_Monodromy_Effectiveness
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
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Digits.Lemmas
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
open Monodromy.AnalyticComparison
open CoupledContinuation
variable {degree : ℕ} [NeZero degree]

theorem Monodromy.AnalyticComparison.eval_embed (program : Program degree) (labels : Labels) :
    eval program (embed labels) = embed <$> program.evalInt labels := by sorry
