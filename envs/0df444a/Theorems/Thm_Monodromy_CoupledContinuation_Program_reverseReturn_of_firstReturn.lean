-- Prove2me | Theorems.Thm_Monodromy_CoupledContinuation_Program_reverseReturn_of_firstReturn
-- name    : Monodromy.CoupledContinuation.Program.reverseReturn_of_firstReturn
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:35:33.170134+00:00
-- url     : https://prove2.me/theorems/3b511fad-7f9a-4d6d-9267-ad8cd2b48652
-- title:
--   Marked Reverse Execution Restores the Start of an Interior Trace
-- statement:
--   Let d>0 and let F,R,B be programs of degree d such that R.advance is a left inverse of F.advance on every coupled state. Suppose F.step(s)=some u, a finite possibly empty chain of F.steps leads from u to t with B.haltSignal≠1 at every departure state, and B.haltSignal(s)=1. Then reverseReturn R B from t is defined and equals s: first take R.advance once, then evaluate R’s words with B’s stopping bits. No separate boundary-mark hypothesis on t is required.
--
--   Statement dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.haltSignal`, `Monodromy.CoupledContinuation.Program.reverseReturn`, `Monodromy.CoupledContinuation.Program.step`.
--
--   Original proof dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.boundaryInverse`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.CoupledContinuation.Program.haltSignal`, `Monodromy.CoupledContinuation.Program.reverseReturn`, `Monodromy.CoupledContinuation.Program.step`.
--
--   Statement elaboration dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.haltSignal`, `Monodromy.CoupledContinuation.Program.reverseReturn`, `Monodromy.CoupledContinuation.Program.step`.
--
--   Proof elaboration dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.boundaryInverse`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.CoupledContinuation.Program.haltSignal`, `Monodromy.CoupledContinuation.Program.reverseReturn`, `Monodromy.CoupledContinuation.Program.step`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Continuation.lean (file SHA-256 c41996cad30503403fe284de8929124f849aa5fd0aaba5433e5e0d4d36fec912):
--   Monodromy.CoupledContinuation.Program.reverseReturn_of_firstReturn at L3073-L3104 [UTF-8 154678:156431].

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
open Monodromy.CoupledContinuation.Program
variable {degree : ℕ} [NeZero degree]

theorem Monodromy.CoupledContinuation.Program.reverseReturn_of_firstReturn (forward backward boundary : Program degree)
    (inverse : Function.LeftInverse backward.advance forward.advance)
    {first after last : Memory} (initial : forward.step first = some after)
    (interior : Relation.ReflTransGen
      (fun left right => forward.step left = some right ∧ boundary.haltSignal left ≠ 1)
      after last)
    (marked : boundary.haltSignal first = 1) :
    reverseReturn backward boundary last = Part.some first := by sorry
