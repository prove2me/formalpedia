-- Prove2me | Theorems.Thm_Monodromy_NativeTuring_macroStep_iota
-- name    : Monodromy.NativeTuring.macroStep_iota
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:49:34.828338+00:00
-- url     : https://prove2.me/theorems/b6a11931-ed40-4628-9491-2355dd457f7c
-- title:
--   The Native First-Return Macro Returns the Exact Optional Turing Step
-- statement:
--   For positive naturals a,q, every Turing machine m over Fin a and Fin q, and every complete configuration x, the causally executed native macro at its specified encoding I(x) is the defined partial value obtained by mapping I over TM0.step(m,x). It therefore returns the optional result none for a halted configuration and some I(y) for a successful source step to y.
--
--   Statement dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.NativeTuring.iota`, `Monodromy.NativeTuring.macroStep`.
--
--   Original proof dependencies: `Monodromy.Counter.Compression.size`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.NativeTuring.FirstReturn`, `Monodromy.NativeTuring.InternalReaches`, `Monodromy.NativeTuring.boundaryProgram`, `Monodromy.NativeTuring.boundary_iota`, `Monodromy.NativeTuring.boundary_stops`, `Monodromy.NativeTuring.internal_marked_reaches`, `Monodromy.NativeTuring.iota`, `Monodromy.NativeTuring.macroStep`, `Monodromy.NativeTuring.program`, `Monodromy.NativeTuring.source2_nonempty`, `Monodromy.NativeTuring.source3`, `Monodromy.NativeTuring.step_firstReturn`, `Monodromy.NativeTuring.step_halt`.
--
--   Statement elaboration dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.NativeTuring.iota`, `Monodromy.NativeTuring.macroStep`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Compression.size`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.NativeTuring.FirstReturn`, `Monodromy.NativeTuring.InternalReaches`, `Monodromy.NativeTuring.boundaryProgram`, `Monodromy.NativeTuring.boundary_iota`, `Monodromy.NativeTuring.boundary_stops`, `Monodromy.NativeTuring.internal_marked_reaches`, `Monodromy.NativeTuring.iota`, `Monodromy.NativeTuring.macroStep`, `Monodromy.NativeTuring.program`, `Monodromy.NativeTuring.source2_nonempty`, `Monodromy.NativeTuring.source3`, `Monodromy.NativeTuring.step_firstReturn`, `Monodromy.NativeTuring.step_halt`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/FormalCompilation.lean (file SHA-256 c07335814044367fc4605d1e494fe82a30c684f754d58d55aaa7514b94c37122):
--   Monodromy.NativeTuring.macroStep_iota at L669-L683 [UTF-8 34154:35100].

module
public import Definitions.Def_Monodromy_FormalCompilation
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
public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
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
open Monodromy.NativeTuring
open Turing CoupledContinuation
variable (a q : ℕ) [NeZero a] [NeZero q]

theorem Monodromy.NativeTuring.macroStep_iota (machine : TM0.Machine (Fin a) (Fin q)) (state : TM0.Cfg (Fin a) (Fin q)) :
    macroStep a q machine (iota a q machine state) =
      Part.some ((TM0.step machine state).map (iota a q machine)) := by sorry
