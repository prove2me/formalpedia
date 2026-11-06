-- Prove2me | Theorems.Thm_Monodromy_Counter_Compression_step_firstReturn
-- name    : Monodromy.Counter.Compression.step_firstReturn
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:44:43.120863+00:00
-- url     : https://prove2.me/theorems/4933c7fe-265d-4424-a4c5-9a7f275b34be
-- title:
--   Prime compression turns a three-counter step into a first return
-- statement:
--   For every natural control size m and three-natural-counter program P, each successful source transition s→t becomes a first return from encode(s) to encode(t) in its two-counter compression. The encoding stores the source registers as $2^{x_0}3^{x_1}5^{x_2}$ and a zero workspace at a dispatch address. The return consists of one successful compiled step followed by a finite possibly empty chain whose departure addresses avoid all source dispatches.
--
--   Statement dependencies: `Monodromy.Counter.Compression.FirstReturn`, `Monodromy.Counter.Compression.encode`, `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.step`.
--
--   Original proof dependencies: `Monodromy.Counter.Compression.FirstReturn`, `Monodromy.Counter.Compression.dec_succ_firstReturn`, `Monodromy.Counter.Compression.dec_zero_firstReturn`, `Monodromy.Counter.Compression.encode`, `Monodromy.Counter.Compression.inc_firstReturn`, `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.Counter.step`, `Monodromy.Counter.step_dec_succ`, `Monodromy.Counter.step_dec_zero`, `Monodromy.Counter.step_inc`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Compression.FirstReturn`, `Monodromy.Counter.Compression.encode`, `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.step`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Compression.FirstReturn`, `Monodromy.Counter.Compression.dec_succ_firstReturn`, `Monodromy.Counter.Compression.dec_zero_firstReturn`, `Monodromy.Counter.Compression.encode`, `Monodromy.Counter.Compression.inc_firstReturn`, `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.Counter.step`, `Monodromy.Counter.step_dec_succ`, `Monodromy.Counter.step_dec_zero`, `Monodromy.Counter.step_inc`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Compression.step_firstReturn at L2394-L2418 [UTF-8 117244:118786].

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
open Monodromy.Counter.Compression
variable {m : ℕ}

theorem Monodromy.Counter.Compression.step_firstReturn (source : Program 3 m) {first last : Configuration 3 m}
    (transition : step source first = some last) :
    FirstReturn source (encode source first) (encode source last) := by sorry
