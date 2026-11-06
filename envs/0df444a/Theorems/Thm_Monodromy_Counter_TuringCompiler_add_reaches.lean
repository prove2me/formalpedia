-- Prove2me | Theorems.Thm_Monodromy_Counter_TuringCompiler_add_reaches
-- name    : Monodromy.Counter.TuringCompiler.add_reaches
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:32:32.751496+00:00
-- url     : https://prove2.me/theorems/ba83162e-933a-410b-9a54-2b874658dbff
-- title:
--   The head-digit countdown enters the division macro
-- statement:
--   Let a,q be positive and suppose a TM0 machine selects a move in direction d from row to target state t. For any countdown digit r<a and natural values v,w, its three-counter table internally reaches the move’s division consume-zero entry from add(row,r), changing the push register from v to v+r while retaining the spectator w and zero scratch. All departure addresses along this finite run are outside the source dispatch set.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.DivMod.consume`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.Row`, `Monodromy.Counter.TuringCompiler.add`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.base_neZero`, `Monodromy.Counter.TuringCompiler.divTarget`, `Monodromy.Counter.TuringCompiler.frame`, `Monodromy.Counter.TuringCompiler.pushRegister`, `Monodromy.Counter.TuringCompiler.size`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.DivMod.consume`, `Monodromy.Counter.DivMod.program`, `Monodromy.Counter.DivMod.size`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.RegisterRelocation.instruction`, `Monodromy.Counter.RegisterRelocation.pairIntoThree`, `Monodromy.Counter.TuringCompiler.Address`, `Monodromy.Counter.TuringCompiler.Boundary`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.InternalStep`, `Monodromy.Counter.TuringCompiler.Phase`, `Monodromy.Counter.TuringCompiler.Row`, `Monodromy.Counter.TuringCompiler.add`, `Monodromy.Counter.TuringCompiler.add_not_boundary`, `Monodromy.Counter.TuringCompiler.address`, `Monodromy.Counter.TuringCompiler.address_add`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.base_neZero`, `Monodromy.Counter.TuringCompiler.dispatch`, `Monodromy.Counter.TuringCompiler.divTarget`, `Monodromy.Counter.TuringCompiler.frame`, `Monodromy.Counter.TuringCompiler.frame_increment`, `Monodromy.Counter.TuringCompiler.frame_scratch`, `Monodromy.Counter.TuringCompiler.mulTarget`, `Monodromy.Counter.TuringCompiler.popRegister`, `Monodromy.Counter.TuringCompiler.previous`, `Monodromy.Counter.TuringCompiler.program`, `Monodromy.Counter.TuringCompiler.pushRegister`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.Counter.mapInstruction`, `Monodromy.Counter.step`, `Monodromy.Counter.step_dec_zero`, `Monodromy.Counter.step_inc`, `Monodromy.CounterMultiplication.program`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.DivMod.consume`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.Row`, `Monodromy.Counter.TuringCompiler.add`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.base_neZero`, `Monodromy.Counter.TuringCompiler.divTarget`, `Monodromy.Counter.TuringCompiler.frame`, `Monodromy.Counter.TuringCompiler.pushRegister`, `Monodromy.Counter.TuringCompiler.size`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.DivMod.consume`, `Monodromy.Counter.DivMod.program`, `Monodromy.Counter.DivMod.size`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.RegisterRelocation.instruction`, `Monodromy.Counter.RegisterRelocation.pairIntoThree`, `Monodromy.Counter.TuringCompiler.Address`, `Monodromy.Counter.TuringCompiler.Boundary`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.InternalStep`, `Monodromy.Counter.TuringCompiler.Phase`, `Monodromy.Counter.TuringCompiler.Row`, `Monodromy.Counter.TuringCompiler.add`, `Monodromy.Counter.TuringCompiler.add_not_boundary`, `Monodromy.Counter.TuringCompiler.address`, `Monodromy.Counter.TuringCompiler.address_add`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.base_neZero`, `Monodromy.Counter.TuringCompiler.body`, `Monodromy.Counter.TuringCompiler.dispatch`, `Monodromy.Counter.TuringCompiler.divTarget`, `Monodromy.Counter.TuringCompiler.frame`, `Monodromy.Counter.TuringCompiler.frame_increment`, `Monodromy.Counter.TuringCompiler.frame_scratch`, `Monodromy.Counter.TuringCompiler.mulTarget`, `Monodromy.Counter.TuringCompiler.popRegister`, `Monodromy.Counter.TuringCompiler.previous`, `Monodromy.Counter.TuringCompiler.program`, `Monodromy.Counter.TuringCompiler.pushRegister`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.Counter.mapInstruction`, `Monodromy.Counter.step`, `Monodromy.Counter.step_dec_zero`, `Monodromy.Counter.step_inc`, `Monodromy.CounterMultiplication.program`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.TuringCompiler.add_reaches at L1822-L1871 [UTF-8 86283:89104].

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

theorem Monodromy.Counter.TuringCompiler.add_reaches (machine : TM0.Machine (Fin a) (Fin q))
    (row : Row a q) (target : Fin q) (direction : Dir)
    (selected : machine row.1 row.2 = some (target, .move direction))
    (remaining : Fin a) (value spectator : ℕ) :
    InternalReaches a q machine
      ⟨add a q row remaining, frame (pushRegister direction) value spectator⟩
      ⟨divTarget a q row target (DivMod.consume (base a) 0),
        frame (pushRegister direction) (value + remaining.val) spectator⟩ := by sorry
