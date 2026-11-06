-- Prove2me | Theorems.Thm_Monodromy_ReversibleRouting_run_pair
-- name    : Monodromy.ReversibleRouting.run_pair
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:38:21.44332+00:00
-- url     : https://prove2.me/theorems/11f1935f-0ac5-447c-a97e-f8222c7bef59
-- title:
--   Distinct guard stages exchange an enabled owner-port pair
-- statement:
--   Let q,e be natural with q+e nonzero, let T be a two-integer-counter table, and assign each edge an owner vertex. Assume ownership is injective within each guard class and distinct edges with the same owner have complementary tests of the same register. For any integer register vector v, enabled edge j, and duplicate-free list of guard stages, running the corresponding native routing stages exchanges the prepared owner(j) state and edge-port q+j state exactly when the guard of j occurs in the list; otherwise both states are fixed. Both conclusions retain v, and the list may be empty.
--
--   Statement dependencies: `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Table`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.ReversibleControl.Guard`, `Monodromy.ReversiblePorts.Matching`, `Monodromy.ReversiblePorts.actionGuard`, `Monodromy.ReversiblePorts.selected`, `Monodromy.ReversibleRouting.CompatibleOwner`, `Monodromy.ReversibleRouting.point`, `Monodromy.ReversibleRouting.run`.
--
--   Original proof dependencies: `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Table`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.ReversibleControl.Guard`, `Monodromy.ReversiblePorts.Matching`, `Monodromy.ReversiblePorts.actionGuard`, `Monodromy.ReversiblePorts.selected`, `Monodromy.ReversibleRouting.CompatibleOwner`, `Monodromy.ReversibleRouting.point`, `Monodromy.ReversibleRouting.route`, `Monodromy.ReversibleRouting.route_owner`, `Monodromy.ReversibleRouting.route_port`, `Monodromy.ReversibleRouting.run`, `Monodromy.ReversibleRouting.run_cons`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Table`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.ReversibleControl.Guard`, `Monodromy.ReversiblePorts.Matching`, `Monodromy.ReversiblePorts.actionGuard`, `Monodromy.ReversiblePorts.selected`, `Monodromy.ReversibleRouting.CompatibleOwner`, `Monodromy.ReversibleRouting.point`, `Monodromy.ReversibleRouting.run`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Table`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.ReversibleControl.Guard`, `Monodromy.ReversiblePorts.Matching`, `Monodromy.ReversiblePorts.actionGuard`, `Monodromy.ReversiblePorts.selected`, `Monodromy.ReversibleRouting.CompatibleOwner`, `Monodromy.ReversibleRouting.point`, `Monodromy.ReversibleRouting.route`, `Monodromy.ReversibleRouting.route_owner`, `Monodromy.ReversibleRouting.route_port`, `Monodromy.ReversibleRouting.run`, `Monodromy.ReversibleRouting.run_cons`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.ReversibleRouting.run_pair at L3241-L3270 [UTF-8 157427:159164].

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
open Monodromy.ReversibleRouting
open CoupledContinuation Counter.Reversible ReversiblePorts
variable {q e : ℕ} [NeZero (q + e)]
variable (table : Table 2 q e) (owner : Fin e → Fin q)
  (matching : ∀ guard, Matching owner (selected table guard))

theorem Monodromy.ReversibleRouting.run_pair (compatible : CompatibleOwner table owner) (values : Fin 2 → ℤ)
    (edge : Fin e) (enabled : (table edge).action.enabled values)
    (stages : List ReversibleControl.Guard) (distinct : stages.Nodup) :
    (run table owner matching stages (point values (Fin.castAdd e (owner edge))) =
      if actionGuard (table edge).action ∈ stages then point values (Fin.natAdd q edge)
      else point values (Fin.castAdd e (owner edge))) ∧
    (run table owner matching stages (point values (Fin.natAdd q edge)) =
      if actionGuard (table edge).action ∈ stages then point values (Fin.castAdd e (owner edge))
      else point values (Fin.natAdd q edge)) := by sorry
