-- Prove2me | Theorems.Thm_Monodromy_Counter_TuringCompiler_move_reaches
-- name    : Monodromy.Counter.TuringCompiler.move_reaches
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:45:54.968463+00:00
-- url     : https://prove2.me/theorems/2db85882-247b-4877-90a1-843ff14cbbc2
-- title:
--   A Turing tape move is realized by internal arithmetic
-- statement:
--   For positive alphabet and state sizes a,q, let M select a move in direction d to target t at a complete TM0 configuration s. Starting at the multiplication entry for (s.state,s.head) with the counters of encode(s), the three-counter table internally reaches the exact encoding of the configuration with state t and tape s.tape moved in direction d. Every departure state in this finite arithmetic run is outside the source dispatch set.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.encode`, `Monodromy.Counter.TuringCompiler.mulTarget`, `Monodromy.Counter.TuringCompiler.size`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.DivMod.consume`, `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.InternalStep`, `Monodromy.Counter.TuringCompiler.add`, `Monodromy.Counter.TuringCompiler.add_reaches`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.base_neZero`, `Monodromy.Counter.TuringCompiler.counters`, `Monodromy.Counter.TuringCompiler.dispatch`, `Monodromy.Counter.TuringCompiler.divTarget`, `Monodromy.Counter.TuringCompiler.divide_reaches`, `Monodromy.Counter.TuringCompiler.encode`, `Monodromy.Counter.TuringCompiler.frame`, `Monodromy.Counter.TuringCompiler.mulTarget`, `Monodromy.Counter.TuringCompiler.multiply_reaches`, `Monodromy.Counter.TuringCompiler.popRegister`, `Monodromy.Counter.TuringCompiler.pushRegister`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.Counter.TuringCompiler.symbol`, `Monodromy.Counter.TuringCompiler.symbol_tape`, `Monodromy.TapeCode.encode`, `Monodromy.TapeCode.encode_cons`, `Monodromy.TapeCode.tail_code`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.encode`, `Monodromy.Counter.TuringCompiler.mulTarget`, `Monodromy.Counter.TuringCompiler.size`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.DivMod.consume`, `Monodromy.Counter.DivMod.residue`, `Monodromy.Counter.TuringCompiler.InternalReaches`, `Monodromy.Counter.TuringCompiler.InternalStep`, `Monodromy.Counter.TuringCompiler.add`, `Monodromy.Counter.TuringCompiler.add_reaches`, `Monodromy.Counter.TuringCompiler.base`, `Monodromy.Counter.TuringCompiler.base_neZero`, `Monodromy.Counter.TuringCompiler.counters`, `Monodromy.Counter.TuringCompiler.dispatch`, `Monodromy.Counter.TuringCompiler.divTarget`, `Monodromy.Counter.TuringCompiler.divide_reaches`, `Monodromy.Counter.TuringCompiler.encode`, `Monodromy.Counter.TuringCompiler.frame`, `Monodromy.Counter.TuringCompiler.mulTarget`, `Monodromy.Counter.TuringCompiler.multiply_reaches`, `Monodromy.Counter.TuringCompiler.popRegister`, `Monodromy.Counter.TuringCompiler.pushRegister`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.Counter.TuringCompiler.symbol`, `Monodromy.Counter.TuringCompiler.symbol_tape`, `Monodromy.TapeCode.encode`, `Monodromy.TapeCode.encode_cons`, `Monodromy.TapeCode.tail_code`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.TuringCompiler.move_reaches at L1884-L1917 [UTF-8 89552:91844].

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

theorem Monodromy.Counter.TuringCompiler.move_reaches (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (target : Fin q) (direction : Dir)
    (selected : machine state.q state.Tape.head = some (target, .move direction)) :
    InternalReaches a q machine
      ⟨mulTarget a q (state.q, state.Tape.head) 0, (encode a q state).counters⟩
      (encode a q ⟨target, state.Tape.move direction⟩) := by sorry
