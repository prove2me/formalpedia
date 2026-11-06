-- Prove2me | Theorems.Thm_Monodromy_StagedProgram_cycle_reaches
-- name    : Monodromy.StagedProgram.cycle_reaches
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:43:53.72518+00:00
-- url     : https://prove2.me/theorems/d1371604-7524-481e-a2ba-28c1896872ad
-- title:
--   An Unmarked Phase-Zero Address Completes a Positive Stage Run
-- statement:
--   For positive naturals c,d, any stages P:Fin c→Program d, Boolean marks b:Fin d→Bool, integers ℓ,r,q and address j∈Fin d with b(j)=false, there is a nonempty successful step run of the marked staged compiler from the phase-zero embedding of prepare(ℓ,r,dq+j) to the phase-zero embedding obtained by applying all stage advances in their listed order to that prepared state.
--
--   Statement dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.StagedProgram.embed`, `Monodromy.StagedProgram.markedCompile`.
--
--   Original proof dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.StagedProgram.advance_embed`, `Monodromy.StagedProgram.compile`, `Monodromy.StagedProgram.cycle_ofFn`, `Monodromy.StagedProgram.embed`, `Monodromy.StagedProgram.interior_step`, `Monodromy.StagedProgram.iterate_embed`, `Monodromy.StagedProgram.markedCompile`, `Monodromy.StagedProgram.positive_reaches_iterate`, `Monodromy.StagedProgram.rotated_zero_ne_zero`, `Monodromy.StagedProgram.step_embed`.
--
--   Statement elaboration dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.StagedProgram.embed`, `Monodromy.StagedProgram.markedCompile`.
--
--   Proof elaboration dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.StagedProgram.advance_embed`, `Monodromy.StagedProgram.compile`, `Monodromy.StagedProgram.cycle_ofFn`, `Monodromy.StagedProgram.embed`, `Monodromy.StagedProgram.interior_step`, `Monodromy.StagedProgram.iterate_embed`, `Monodromy.StagedProgram.markedCompile`, `Monodromy.StagedProgram.positive_reaches_iterate`, `Monodromy.StagedProgram.rotated_zero_ne_zero`, `Monodromy.StagedProgram.step_embed`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Continuation.lean (file SHA-256 c41996cad30503403fe284de8929124f849aa5fd0aaba5433e5e0d4d36fec912):
--   Monodromy.StagedProgram.cycle_reaches at L2946-L2974 [UTF-8 147659:149359].

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
open Monodromy.StagedProgram
open CoupledContinuation
open Fin.NatCast
variable (count degree : ℕ) [NeZero count] [NeZero degree]

theorem Monodromy.StagedProgram.cycle_reaches (stages : Fin count → Program degree) (mark : Fin degree → Bool)
    (left right quotient : ℤ) (index : Fin degree) (unmarked : mark index = false) :
    StateTransition.Reaches₁ (markedCompile count degree stages mark).step
      (embed count 0 (prepare left right ((degree : ℤ) * quotient + index.val)))
      (embed count 0 ((List.ofFn stages).foldl (fun point stage => stage.advance point)
        (prepare left right ((degree : ℤ) * quotient + index.val)))) := by sorry
