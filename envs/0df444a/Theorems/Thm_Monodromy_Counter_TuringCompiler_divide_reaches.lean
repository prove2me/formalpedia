-- Prove2me | Theorems.Thm_Monodromy_Counter_TuringCompiler_divide_reaches
-- name    : Monodromy.Counter.TuringCompiler.divide_reaches
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:41:17.721703+00:00
-- url     : https://prove2.me/theorems/7d2aa8dd-2b43-4682-a7af-f7b7548ec9d3
-- title:
--   A Turing move division macro returns the new head
-- statement:
--   Let a,q be positive and suppose a TM0 machine selects a move in direction d from row=(σ,h) to target state t. For any natural pop-register value v and spectator w, the compiled three-counter table has an internal run from the division consume-zero entry for that move to the dispatch for t and the decoded remainder of v modulo a+1, with pop register ⌊v/(a+1)⌋, spectator w and scratch 0. The unused remainder a is decoded as blank 0, and every departure state of the run is outside the dispatch set.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.DivMod.consume`, `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.Row`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.base_neZero`, `Monodromy.Counter.TuringCompiler.dispatch`, `Monodromy.Counter.TuringCompiler.divTarget`, `Monodromy.Counter.TuringCompiler.frame`, `Monodromy.Counter.TuringCompiler.popRegister`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.Counter.TuringCompiler.symbol`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.DivMod.configuration`, `Monodromy.Counter.DivMod.consume`, `Monodromy.Counter.DivMod.finish`, `Monodromy.Counter.DivMod.program`, `Monodromy.Counter.DivMod.reaches_divmod`, `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.DivMod.size`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.RegisterRelocation.embed`, `Monodromy.Counter.RegisterRelocation.pairIntoThree`, `Monodromy.Counter.RegisterRelocation.pairIntoThree_injective`, `Monodromy.Counter.RegisterRelocation.program`, `Monodromy.Counter.RegisterRelocation.reaches_embed`, `Monodromy.Counter.TuringCompiler.Boundary`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.Row`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.base_neZero`, `Monodromy.Counter.TuringCompiler.dispatch`, `Monodromy.Counter.TuringCompiler.divTarget`, `Monodromy.Counter.TuringCompiler.divTarget_finish`, `Monodromy.Counter.TuringCompiler.div_live`, `Monodromy.Counter.TuringCompiler.extend_frame`, `Monodromy.Counter.TuringCompiler.frame`, `Monodromy.Counter.TuringCompiler.map_internal`, `Monodromy.Counter.TuringCompiler.popRegister`, `Monodromy.Counter.TuringCompiler.program`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.Counter.TuringCompiler.symbol`, `Monodromy.Counter.mapConfiguration`, `Monodromy.Counter.mapInstruction`, `Monodromy.Counter.step`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.DivMod.consume`, `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.Row`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.base_neZero`, `Monodromy.Counter.TuringCompiler.dispatch`, `Monodromy.Counter.TuringCompiler.divTarget`, `Monodromy.Counter.TuringCompiler.frame`, `Monodromy.Counter.TuringCompiler.popRegister`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.Counter.TuringCompiler.symbol`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.DivMod.configuration`, `Monodromy.Counter.DivMod.consume`, `Monodromy.Counter.DivMod.finish`, `Monodromy.Counter.DivMod.program`, `Monodromy.Counter.DivMod.reaches_divmod`, `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.DivMod.size`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.RegisterRelocation.embed`, `Monodromy.Counter.RegisterRelocation.pairIntoThree`, `Monodromy.Counter.RegisterRelocation.pairIntoThree_injective`, `Monodromy.Counter.RegisterRelocation.program`, `Monodromy.Counter.RegisterRelocation.reaches_embed`, `Monodromy.Counter.TuringCompiler.Boundary`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.Row`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.base_neZero`, `Monodromy.Counter.TuringCompiler.dispatch`, `Monodromy.Counter.TuringCompiler.divTarget`, `Monodromy.Counter.TuringCompiler.divTarget_finish`, `Monodromy.Counter.TuringCompiler.div_live`, `Monodromy.Counter.TuringCompiler.extend_frame`, `Monodromy.Counter.TuringCompiler.frame`, `Monodromy.Counter.TuringCompiler.map_internal`, `Monodromy.Counter.TuringCompiler.popRegister`, `Monodromy.Counter.TuringCompiler.program`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.Counter.TuringCompiler.symbol`, `Monodromy.Counter.mapConfiguration`, `Monodromy.Counter.mapInstruction`, `Monodromy.Counter.step`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.TuringCompiler.divide_reaches at L1791-L1811 [UTF-8 84501:85809].

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

theorem Monodromy.Counter.TuringCompiler.divide_reaches (machine : TM0.Machine (Fin a) (Fin q))
    (row : Row a q) (target : Fin q) (direction : Dir)
    (selected : machine row.1 row.2 = some (target, .move direction))
    (value spectator : ℕ) :
    InternalReaches a q machine
      ⟨divTarget a q row target (DivMod.consume (base a) 0),
        frame (popRegister direction) value spectator⟩
      ⟨dispatch a q (target, symbol a (DivMod.residue (base a) value)),
        frame (popRegister direction) (value / base a) spectator⟩ := by sorry
