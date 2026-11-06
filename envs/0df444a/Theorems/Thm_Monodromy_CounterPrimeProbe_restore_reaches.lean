-- Prove2me | Theorems.Thm_Monodromy_CounterPrimeProbe_restore_reaches
-- name    : Monodromy.CounterPrimeProbe.restore_reaches
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:42:19.456263+00:00
-- url     : https://prove2.me/theorems/32d88237-882e-4e8f-9b91-7fcaaae71dde
-- title:
--   The probe restoration path reconstructs quotient and remainder
-- statement:
--   For every positive p, remainder r<p, and natural quotient q, the two-counter probe program has a finite run from the multiplication countdown address phase(p,r) with counters (q,0) to its failure address with counters (r+p·q,0). The theorem allows r=0 as well as nonzero remainders.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.step`, `Monodromy.CounterMultiplication.phase`, `Monodromy.CounterPrimeProbe.configuration`, `Monodromy.CounterPrimeProbe.failure`, `Monodromy.CounterPrimeProbe.mulAddress`, `Monodromy.CounterPrimeProbe.program`, `Monodromy.CounterPrimeProbe.size`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.mapConfiguration`, `Monodromy.Counter.reaches_map_live`, `Monodromy.Counter.step`, `Monodromy.CounterMultiplication.configuration`, `Monodromy.CounterMultiplication.consume_reach`, `Monodromy.CounterMultiplication.finish`, `Monodromy.CounterMultiplication.increments_reach`, `Monodromy.CounterMultiplication.phase`, `Monodromy.CounterMultiplication.program`, `Monodromy.CounterMultiplication.step_begin_transfer`, `Monodromy.CounterMultiplication.step_finish`, `Monodromy.CounterMultiplication.transfer`, `Monodromy.CounterMultiplication.transfer_reach`, `Monodromy.CounterPrimeProbe.configuration`, `Monodromy.CounterPrimeProbe.failure`, `Monodromy.CounterPrimeProbe.mulAddress`, `Monodromy.CounterPrimeProbe.program`, `Monodromy.CounterPrimeProbe.program_mulAddress`, `Monodromy.CounterPrimeProbe.size`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.step`, `Monodromy.CounterMultiplication.phase`, `Monodromy.CounterPrimeProbe.configuration`, `Monodromy.CounterPrimeProbe.failure`, `Monodromy.CounterPrimeProbe.mulAddress`, `Monodromy.CounterPrimeProbe.program`, `Monodromy.CounterPrimeProbe.size`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.mapConfiguration`, `Monodromy.Counter.reaches_map_live`, `Monodromy.Counter.step`, `Monodromy.CounterMultiplication.configuration`, `Monodromy.CounterMultiplication.consume_reach`, `Monodromy.CounterMultiplication.finish`, `Monodromy.CounterMultiplication.increments_reach`, `Monodromy.CounterMultiplication.phase`, `Monodromy.CounterMultiplication.program`, `Monodromy.CounterMultiplication.step_begin_transfer`, `Monodromy.CounterMultiplication.step_finish`, `Monodromy.CounterMultiplication.transfer`, `Monodromy.CounterMultiplication.transfer_reach`, `Monodromy.CounterPrimeProbe.configuration`, `Monodromy.CounterPrimeProbe.failure`, `Monodromy.CounterPrimeProbe.mulAddress`, `Monodromy.CounterPrimeProbe.mul_configuration`, `Monodromy.CounterPrimeProbe.program`, `Monodromy.CounterPrimeProbe.program_mulAddress`, `Monodromy.CounterPrimeProbe.size`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.CounterPrimeProbe.restore_reaches at L1370-L1390 [UTF-8 64761:66290].

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
open Monodromy.CounterPrimeProbe
variable (p : ℕ) [NeZero p]

theorem Monodromy.CounterPrimeProbe.restore_reaches (remainder : Fin p) (quotient : ℕ) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (mulAddress p (CounterMultiplication.phase p remainder.val)) quotient 0)
      (configuration p (Monodromy.CounterPrimeProbe.failure p) (remainder.val + p * quotient) 0) := by sorry
