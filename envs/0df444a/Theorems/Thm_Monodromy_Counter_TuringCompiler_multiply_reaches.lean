-- Prove2me | Theorems.Thm_Monodromy_Counter_TuringCompiler_multiply_reaches
-- name    : Monodromy.Counter.TuringCompiler.multiply_reaches
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:41:34.956455+00:00
-- url     : https://prove2.me/theorems/eda743f7-bc51-4ede-87c4-80ed198094ad
-- title:
--   A Turing move multiplication macro preserves the spectator
-- statement:
--   Let a,q be positive, M a TM0 machine over Fin a and Fin q, and row=(σ,h) a source state/head pair for which M selects a move in direction d to state t. For all natural values v,w, its three-counter table has an internal run from the multiplication entry for row, with push register v, other tape register w and scratch 0, to the addition entry for the old head h with push register (a+1)v, spectator w and scratch 0. Every departure state in this internal run is outside the source dispatch set.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.Row`, `Monodromy.Counter.TuringCompiler.add`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.frame`, `Monodromy.Counter.TuringCompiler.mulTarget`, `Monodromy.Counter.TuringCompiler.pushRegister`, `Monodromy.Counter.TuringCompiler.size`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.RegisterRelocation.embed`, `Monodromy.Counter.RegisterRelocation.pairIntoThree`, `Monodromy.Counter.RegisterRelocation.pairIntoThree_injective`, `Monodromy.Counter.RegisterRelocation.program`, `Monodromy.Counter.RegisterRelocation.reaches_embed`, `Monodromy.Counter.TuringCompiler.Boundary`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.Row`, `Monodromy.Counter.TuringCompiler.add`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.extend_frame`, `Monodromy.Counter.TuringCompiler.frame`, `Monodromy.Counter.TuringCompiler.map_internal`, `Monodromy.Counter.TuringCompiler.mulTarget`, `Monodromy.Counter.TuringCompiler.mulTarget_finish`, `Monodromy.Counter.TuringCompiler.mul_live`, `Monodromy.Counter.TuringCompiler.program`, `Monodromy.Counter.TuringCompiler.pushRegister`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.Counter.mapConfiguration`, `Monodromy.Counter.mapInstruction`, `Monodromy.Counter.step`, `Monodromy.CounterMultiplication.configuration`, `Monodromy.CounterMultiplication.finish`, `Monodromy.CounterMultiplication.program`, `Monodromy.CounterMultiplication.reaches_result`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.Row`, `Monodromy.Counter.TuringCompiler.add`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.frame`, `Monodromy.Counter.TuringCompiler.mulTarget`, `Monodromy.Counter.TuringCompiler.pushRegister`, `Monodromy.Counter.TuringCompiler.size`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.RegisterRelocation.embed`, `Monodromy.Counter.RegisterRelocation.pairIntoThree`, `Monodromy.Counter.RegisterRelocation.pairIntoThree_injective`, `Monodromy.Counter.RegisterRelocation.program`, `Monodromy.Counter.RegisterRelocation.reaches_embed`, `Monodromy.Counter.TuringCompiler.Boundary`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.Row`, `Monodromy.Counter.TuringCompiler.add`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.extend_frame`, `Monodromy.Counter.TuringCompiler.frame`, `Monodromy.Counter.TuringCompiler.map_internal`, `Monodromy.Counter.TuringCompiler.mulTarget`, `Monodromy.Counter.TuringCompiler.mulTarget_finish`, `Monodromy.Counter.TuringCompiler.mul_live`, `Monodromy.Counter.TuringCompiler.program`, `Monodromy.Counter.TuringCompiler.pushRegister`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.Counter.mapConfiguration`, `Monodromy.Counter.mapInstruction`, `Monodromy.Counter.step`, `Monodromy.CounterMultiplication.configuration`, `Monodromy.CounterMultiplication.finish`, `Monodromy.CounterMultiplication.program`, `Monodromy.CounterMultiplication.reaches_result`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.TuringCompiler.multiply_reaches at L1770-L1789 [UTF-8 83243:84499].

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
open Monodromy.Counter.TuringCompiler
open Turing
variable (a q : ℕ) [NeZero a] [NeZero q]

theorem Monodromy.Counter.TuringCompiler.multiply_reaches (machine : TM0.Machine (Fin a) (Fin q))
    (row : Row a q) (target : Fin q) (direction : Dir)
    (selected : machine row.1 row.2 = some (target, .move direction))
    (value spectator : ℕ) :
    InternalReaches a q machine
      ⟨mulTarget a q row 0, frame (pushRegister direction) value spectator⟩
      ⟨add a q row row.2, frame (pushRegister direction) (base a * value) spectator⟩ := by sorry
