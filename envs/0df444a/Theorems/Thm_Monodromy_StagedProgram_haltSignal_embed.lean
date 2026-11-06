-- Prove2me | Theorems.Thm_Monodromy_StagedProgram_haltSignal_embed
-- name    : Monodromy.StagedProgram.haltSignal_embed
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:38:55.281212+00:00
-- url     : https://prove2.me/theorems/f1d811c5-573f-4bee-a51b-7a0d69148358
-- title:
--   Packed Stopping Signals Read Only Marked Phase-Zero Addresses
-- statement:
--   For positive naturals c,d, any stages P:Fin c→Program d, any Boolean address marks b:Fin d→Bool, integers ℓ,r,q, address j∈Fin d and phase k∈Fin c, the marked compiler’s halt signal at the phase-k embedding of prepare(ℓ,r,dq+j) is 1 exactly when k=0 and b(j)=true, and is 0 otherwise.
--
--   Statement dependencies: `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.haltSignal`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.StagedProgram.embed`, `Monodromy.StagedProgram.markedCompile`.
--
--   Original proof dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.haltSignal`, `Monodromy.CoupledContinuation.Program.haltSignal_prepare`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.StagedProgram.address`, `Monodromy.StagedProgram.address_val`, `Monodromy.StagedProgram.embed`, `Monodromy.StagedProgram.embed_prepare`, `Monodromy.StagedProgram.markedCompile`, `Monodromy.StagedProgram.markedCompile_stop_address`.
--
--   Statement elaboration dependencies: `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.haltSignal`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.StagedProgram.embed`, `Monodromy.StagedProgram.markedCompile`.
--
--   Proof elaboration dependencies: `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.haltSignal`, `Monodromy.CoupledContinuation.Program.haltSignal_prepare`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.StagedProgram.address`, `Monodromy.StagedProgram.address_val`, `Monodromy.StagedProgram.embed`, `Monodromy.StagedProgram.embed_prepare`, `Monodromy.StagedProgram.markedCompile`, `Monodromy.StagedProgram.markedCompile_stop_address`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Continuation.lean (file SHA-256 c41996cad30503403fe284de8929124f849aa5fd0aaba5433e5e0d4d36fec912):
--   Monodromy.StagedProgram.haltSignal_embed at L2834-L2852 [UTF-8 141628:142759].

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

theorem Monodromy.StagedProgram.haltSignal_embed (stages : Fin count → Program degree) (mark : Fin degree → Bool)
    (left right quotient : ℤ) (index : Fin degree) (phase : Fin count) :
    (markedCompile count degree stages mark).haltSignal
      (embed count phase (prepare left right ((degree : ℤ) * quotient + index.val))) =
      if (if phase = 0 then mark index else false) then 1 else 0 := by sorry
