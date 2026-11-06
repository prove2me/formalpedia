-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_Glue_controls_eq_iff
-- name    : Monodromy.Counter.Reversible.Glue.controls_eq_iff
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:29:01.944256+00:00
-- url     : https://prove2.me/theorems/91df01ef-c1c0-422a-b49e-a5b5de34861f
-- title:
--   Glued control ranges meet only at the identified interface
-- statement:
--   For arbitrary natural q₁,q₂, select a left exit among q₁+1 addresses and a right entry among q₂ addresses. Map the left exit to the right entry’s slot, all other left addresses to the first q₁ slots, and right addresses to the final q₂ slots. For every left address l and right address r, their mapped addresses are equal if and only if l is the selected exit and r is the selected entry; both equalities are required together.
--
--   Statement dependencies: `Monodromy.Counter.Reversible.Glue.leftControl`, `Monodromy.Counter.Reversible.Glue.rightControl`.
--
--   Original proof dependencies: `Monodromy.Counter.Reversible.Glue.leftControl`, `Monodromy.Counter.Reversible.Glue.leftControl_other`, `Monodromy.Counter.Reversible.Glue.rightControl`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Reversible.Glue.leftControl`, `Monodromy.Counter.Reversible.Glue.rightControl`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Reversible.Glue.leftControl`, `Monodromy.Counter.Reversible.Glue.leftControl_other`, `Monodromy.Counter.Reversible.Glue.rightControl`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.Glue.controls_eq_iff at L4010-L4025 [UTF-8 199405:200153].

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
open Monodromy.Counter.Reversible.Glue
variable {n q₁ q₂ e₁ e₂ : ℕ}

theorem Monodromy.Counter.Reversible.Glue.controls_eq_iff (exit : Fin (q₁ + 1)) (entry : Fin q₂)
    (left : Fin (q₁ + 1)) (right : Fin q₂) :
    leftControl exit entry left = rightControl right ↔ left = exit ∧ right = entry := by sorry
