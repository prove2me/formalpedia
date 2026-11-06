-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_step_iff
-- name    : Monodromy.Counter.Reversible.step_iff
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:32:21.364214+00:00
-- url     : https://prove2.me/theorems/7e06943b-f651-492d-b1d9-2849f4b248b6
-- title:
--   The selected reversible step equals enabled-edge semantics
-- statement:
--   For any natural n,q,e and n-integer-counter table with q control vertices and e edges, assume distinct edges sharing a source have complementary zero/nonzero tests of the same register. For any states s,t, the selected optional step at s equals some t if and only if an edge has source s.pc, is enabled at s, and produces t by moving to its target and applying its shift or unchanged test action.
--
--   Statement dependencies: `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.StepRel`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.step`.
--
--   Original proof dependencies: `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.Edge.instDecidableEnabled`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.StepRel`, `Monodromy.Counter.Reversible.StepRel.deterministic`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.step`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.StepRel`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.step`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.Edge.instDecidableEnabled`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.StepRel`, `Monodromy.Counter.Reversible.StepRel.deterministic`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.step`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.step_iff at L2693-L2705 [UTF-8 131285:131849].

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
variable {n q e : ℕ}

theorem Monodromy.Counter.Reversible.step_iff (table : Table n q e) (deterministic : Deterministic table)
    {first last : State n q} : Monodromy.Counter.Reversible.step table first = some last ↔ StepRel table first last := by sorry
