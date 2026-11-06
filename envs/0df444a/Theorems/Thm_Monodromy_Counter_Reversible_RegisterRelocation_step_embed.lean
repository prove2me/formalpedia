-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_RegisterRelocation_step_embed
-- name    : Monodromy.Counter.Reversible.RegisterRelocation.step_embed
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:41:05.196553+00:00
-- url     : https://prove2.me/theorems/af293320-27ed-4630-825a-f700cc9b0202
-- title:
--   Injective register relocation preserves the complete optional step
-- statement:
--   For arbitrary natural n,m,q,e, embed n integer registers injectively into m registers, filling all unselected registers from any fixed integer background. For a deterministic n-register table with q vertices and e edges, renaming every action by this register injection commutes with its whole optional step on every embedded state: the relocated result is the embedded source result when defined, and is absent exactly when the source result is absent. Here determinism requires complementary same-register tests for distinct edges with a common source.
--
--   Statement dependencies: `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.RegisterRelocation.embed`, `Monodromy.Counter.Reversible.RegisterRelocation.mapTable`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.step`.
--
--   Original proof dependencies: `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.RegisterRelocation.deterministic`, `Monodromy.Counter.Reversible.RegisterRelocation.edge_enabled_embed`, `Monodromy.Counter.Reversible.RegisterRelocation.edge_execute_embed`, `Monodromy.Counter.Reversible.RegisterRelocation.embed`, `Monodromy.Counter.Reversible.RegisterRelocation.mapTable`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.StepRel`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.Reversible.step_iff`, `Monodromy.Counter.Reversible.step_none_iff`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.RegisterRelocation.embed`, `Monodromy.Counter.Reversible.RegisterRelocation.mapTable`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.step`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.RegisterRelocation.deterministic`, `Monodromy.Counter.Reversible.RegisterRelocation.edge_enabled_embed`, `Monodromy.Counter.Reversible.RegisterRelocation.edge_execute_embed`, `Monodromy.Counter.Reversible.RegisterRelocation.embed`, `Monodromy.Counter.Reversible.RegisterRelocation.mapTable`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.StepRel`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.Reversible.step_iff`, `Monodromy.Counter.Reversible.step_none_iff`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.RegisterRelocation.step_embed at L3939-L3956 [UTF-8 196000:197106].

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
open Monodromy.Counter.Reversible.RegisterRelocation
variable {n m q e : ℕ}

theorem Monodromy.Counter.Reversible.RegisterRelocation.step_embed (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (source : Table n q e) (valid : Deterministic source)
    (state : State n q) :
    step (mapTable register source) (embed register background state) =
      (step source state).map (embed register background) := by sorry
