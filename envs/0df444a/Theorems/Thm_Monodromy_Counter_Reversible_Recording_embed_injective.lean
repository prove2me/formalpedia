-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_Recording_embed_injective
-- name    : Monodromy.Counter.Reversible.Recording.embed_injective
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:29:56.537585+00:00
-- url     : https://prove2.me/theorems/32e21e58-393e-4269-85ed-fb6c48b676c6
-- title:
--   Recording into integer registers is injective
-- statement:
--   For arbitrary natural register and control counts n,m, embedding a recorded state (source configuration, natural history) into the reversible table with n+2 integer registers is injective. The embedding retains the source program counter at its recording dispatch, casts all n natural source counters to integers, places the history in the next register and sets the final workspace register to zero.
--
--   Statement dependencies: `Monodromy.Counter.Recorded.State`, `Monodromy.Counter.Reversible.Recording.embed`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.State`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Recorded.State`, `Monodromy.Counter.Reversible.Radix.entry`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Recording.base`, `Monodromy.Counter.Reversible.Recording.copy`, `Monodromy.Counter.Reversible.Recording.copy_eq_iff`, `Monodromy.Counter.Reversible.Recording.dispatch`, `Monodromy.Counter.Reversible.Recording.embed`, `Monodromy.Counter.Reversible.Recording.frame_history`, `Monodromy.Counter.Reversible.Recording.frame_old`, `Monodromy.Counter.Reversible.Recording.framed`, `Monodromy.Counter.Reversible.Recording.historyRegister`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.State`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Recorded.State`, `Monodromy.Counter.Reversible.Recording.embed`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.State`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Recorded.State`, `Monodromy.Counter.Reversible.Radix.entry`, `Monodromy.Counter.Reversible.Radix.size`, `Monodromy.Counter.Reversible.Recording.base`, `Monodromy.Counter.Reversible.Recording.copy`, `Monodromy.Counter.Reversible.Recording.copy_eq_iff`, `Monodromy.Counter.Reversible.Recording.dispatch`, `Monodromy.Counter.Reversible.Recording.embed`, `Monodromy.Counter.Reversible.Recording.frame_history`, `Monodromy.Counter.Reversible.Recording.frame_old`, `Monodromy.Counter.Reversible.Recording.framed`, `Monodromy.Counter.Reversible.Recording.historyRegister`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.State`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.Recording.embed_injective at L5931-L5946 [UTF-8 295662:296611].

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
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Recording
variable {n m : ℕ}

theorem Monodromy.Counter.Reversible.Recording.embed_injective : Function.Injective (@embed n m) := by sorry
