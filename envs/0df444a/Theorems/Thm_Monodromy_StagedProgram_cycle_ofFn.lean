-- Prove2me | Theorems.Thm_Monodromy_StagedProgram_cycle_ofFn
-- name    : Monodromy.StagedProgram.cycle_ofFn
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:38:37.042192+00:00
-- url     : https://prove2.me/theorems/c6763297-4a92-4610-b7fd-aa590eeb7791
-- title:
--   A Complete Packed Cycle Executes the Ordered Stage Tuple
-- statement:
--   For positive natural numbers c,d, any stage tuple P:Fin c→Program d, and any coupled state s, c total advances of the compiled staged program from the phase-zero embedding of s equal the phase-zero embedding of the left fold applying P_0.advance through P_{c−1}.advance to s in order. This statement concerns total advance iteration and imposes no stopping hypothesis.
--
--   Statement dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.StagedProgram.compile`, `Monodromy.StagedProgram.embed`.
--
--   Original proof dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.StagedProgram.compile`, `Monodromy.StagedProgram.cycle`, `Monodromy.StagedProgram.embed`.
--
--   Statement elaboration dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.StagedProgram.compile`, `Monodromy.StagedProgram.embed`.
--
--   Proof elaboration dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.StagedProgram.compile`, `Monodromy.StagedProgram.cycle`, `Monodromy.StagedProgram.embed`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Continuation.lean (file SHA-256 c41996cad30503403fe284de8929124f849aa5fd0aaba5433e5e0d4d36fec912):
--   Monodromy.StagedProgram.cycle_ofFn at L2656-L2671 [UTF-8 132287:133108].

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

theorem Monodromy.StagedProgram.cycle_ofFn (stages : Fin count → Program degree) (state : Memory) :
    ((compile count degree stages).advance)^[count] (embed count 0 state) =
      embed count 0 ((List.ofFn stages).foldl
        (fun point program => program.advance point) state) := by sorry
