-- Prove2me | Theorems.Thm_Monodromy_CounterContinuation_advance_dec_first
-- name    : Monodromy.CounterContinuation.advance_dec_first
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:34:31.845829+00:00
-- url     : https://prove2.me/theorems/fe1b726b-c83b-4130-a085-7cf794a0c084
-- title:
--   Decrement dispatch selects phase one or two
-- statement:
--   For every positive control size m, two-counter program P, address i, register j, and zero/nonzero destinations z and n, suppose P(i) is the decrement instruction on j with destinations z,n. For any integer memory labels x,y, one total advance of the three-phase continuation compilation from prepare(x,y,3i) returns prepare(x,y,3i+1+ε), where ε is 1 when the selected label (x,y)ⱼ is zero and 0 otherwise. Both memory labels are unchanged.
--
--   Statement dependencies: `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.label`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.prepare`.
--
--   Original proof dependencies: `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.CounterContinuation.advance_at`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.instructionWord`, `Monodromy.CounterContinuation.label`, `Monodromy.CounterContinuation.label_eq`, `Monodromy.CounterContinuation.memoryGate`, `Monodromy.CounterContinuation.zeroGate`, `Monodromy.CoupledContinuation.B_left`, `Monodromy.CoupledContinuation.B_right`, `Monodromy.CoupledContinuation.Driver`, `Monodromy.CoupledContinuation.Driver.reverse`, `Monodromy.CoupledContinuation.Gate`, `Monodromy.CoupledContinuation.Gate.driver`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Word`, `Monodromy.CoupledContinuation.Word.atom`, `Monodromy.CoupledContinuation.Word.control`, `Monodromy.CoupledContinuation.Word.driver`, `Monodromy.CoupledContinuation.execute`, `Monodromy.CoupledContinuation.execute_B_left`, `Monodromy.CoupledContinuation.execute_B_right`, `Monodromy.CoupledContinuation.execute_control_word`, `Monodromy.CoupledContinuation.execute_word_append`, `Monodromy.CoupledContinuation.execute_word_atom`, `Monodromy.CoupledContinuation.prepare`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.label`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.prepare`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.CounterContinuation.advance_at`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.instructionWord`, `Monodromy.CounterContinuation.label`, `Monodromy.CounterContinuation.label_eq`, `Monodromy.CounterContinuation.memoryGate`, `Monodromy.CounterContinuation.zeroGate`, `Monodromy.CoupledContinuation.B_left`, `Monodromy.CoupledContinuation.B_right`, `Monodromy.CoupledContinuation.Driver`, `Monodromy.CoupledContinuation.Driver.reverse`, `Monodromy.CoupledContinuation.Gate`, `Monodromy.CoupledContinuation.Gate.driver`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Word`, `Monodromy.CoupledContinuation.Word.atom`, `Monodromy.CoupledContinuation.Word.control`, `Monodromy.CoupledContinuation.Word.driver`, `Monodromy.CoupledContinuation.execute`, `Monodromy.CoupledContinuation.execute_B_left`, `Monodromy.CoupledContinuation.execute_B_right`, `Monodromy.CoupledContinuation.execute_control_word`, `Monodromy.CoupledContinuation.execute_word_append`, `Monodromy.CoupledContinuation.execute_word_atom`, `Monodromy.CoupledContinuation.prepare`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.CounterContinuation.advance_dec_first at L256-L273 [UTF-8 10621:11332].

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
open Monodromy.CounterContinuation
open CoupledContinuation
variable {m : ℕ} [NeZero m]

theorem Monodromy.CounterContinuation.advance_dec_first (program : Counter.Program 2 m) (position zero nonzero : Fin m)
    (register : Fin 2) (instruction : program position = .dec register zero nonzero) (left right : ℤ) :
    (compile program).advance (prepare left right (label position 0)) =
      prepare left right (label position 1 + if (![left, right] register) = 0 then 1 else 0) := by sorry
