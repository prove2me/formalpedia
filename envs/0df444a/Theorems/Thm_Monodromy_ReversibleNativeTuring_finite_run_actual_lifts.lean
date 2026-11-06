-- Prove2me | Theorems.Thm_Monodromy_ReversibleNativeTuring_finite_run_actual_lifts
-- name    : Monodromy.ReversibleNativeTuring.finite_run_actual_lifts
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:53:30.510647+00:00
-- url     : https://prove2.me/theorems/cc243aac-c8fb-488b-8ac1-48f160e7403d
-- title:
--   Every Finite Turing Prefix Has the Two Actual Matching Cover Lifts
-- statement:
--   For positive naturals a,q, a Turing machine m over Fin a and Fin q, configurations x,y, natural history h and a finite possibly zero-length successful source run from x to y, there exist natural h′ and n such that the driver P.runDriver(n,I(x,h)) has its entire intermediate curve equal to the lower-covering lift from the upper projection of the restricted initial state, its entire restricted trajectory equal to the upper-covering lift of that intermediate path from the restricted initial state, and its endpoint equal to the restricted state I(y,h′). A halt, n>0, and h′>h are not required.
--
--   Statement dependencies: `Monodromy.CoupledContinuation.Driver`, `Monodromy.CoupledContinuation.Driver.restrictedPath`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.runDriver`, `Monodromy.CoupledContinuation.intermediateCurve`, `Monodromy.CoupledContinuation.intermediatePath`, `Monodromy.CoupledContinuation.restrictedBase`, `Monodromy.CoupledContinuation.restrictedState`, `Monodromy.CoupledContinuation.restrictedState_over_base`, `Monodromy.CoupledContinuation.restrictedTrajectory`, `Monodromy.CoupledPullback.Base`, `Monodromy.CoupledPullback.Lower`, `Monodromy.CoupledPullback.Point`, `Monodromy.CoupledPullback.Punctured`, `Monodromy.CoupledPullback.Root`, `Monodromy.CoupledPullback.lowerCovering`, `Monodromy.CoupledPullback.lowerProjection`, `Monodromy.CoupledPullback.upperCovering`, `Monodromy.CoupledPullback.upperProjection`, `Monodromy.NestedRestricted.baseSet`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.program`, `Monodromy.ReversibleNativeTuring.size_nonzero`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.size`.
--
--   Original proof dependencies: `Monodromy.CoupledContinuation.Driver`, `Monodromy.CoupledContinuation.Driver.restrictedPath`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.runDriver`, `Monodromy.CoupledContinuation.Program.runDriver_of_reaches`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.CoupledContinuation.execute`, `Monodromy.CoupledContinuation.intermediateCurve`, `Monodromy.CoupledContinuation.intermediateCurve_actual_lift`, `Monodromy.CoupledContinuation.intermediatePath`, `Monodromy.CoupledContinuation.restrictedBase`, `Monodromy.CoupledContinuation.restrictedState`, `Monodromy.CoupledContinuation.restrictedState_over_base`, `Monodromy.CoupledContinuation.restrictedTrajectory`, `Monodromy.CoupledContinuation.restrictedTrajectory_actual_lift`, `Monodromy.CoupledContinuation.restrictedTrajectory_end`, `Monodromy.CoupledPullback.Base`, `Monodromy.CoupledPullback.Lower`, `Monodromy.CoupledPullback.Point`, `Monodromy.CoupledPullback.Punctured`, `Monodromy.CoupledPullback.Root`, `Monodromy.CoupledPullback.lowerCovering`, `Monodromy.CoupledPullback.lowerProjection`, `Monodromy.CoupledPullback.upperCovering`, `Monodromy.CoupledPullback.upperProjection`, `Monodromy.NestedRestricted.baseSet`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleNativeTuring.Related`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.program`, `Monodromy.ReversibleNativeTuring.respects`, `Monodromy.ReversibleNativeTuring.size_nonzero`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.size`.
--
--   Statement elaboration dependencies: `Monodromy.CoupledContinuation.Driver`, `Monodromy.CoupledContinuation.Driver.restrictedPath`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.runDriver`, `Monodromy.CoupledContinuation.intermediateCurve`, `Monodromy.CoupledContinuation.intermediatePath`, `Monodromy.CoupledContinuation.restrictedBase`, `Monodromy.CoupledContinuation.restrictedState`, `Monodromy.CoupledContinuation.restrictedState_over_base`, `Monodromy.CoupledContinuation.restrictedTrajectory`, `Monodromy.CoupledPullback.Base`, `Monodromy.CoupledPullback.Lower`, `Monodromy.CoupledPullback.Point`, `Monodromy.CoupledPullback.Punctured`, `Monodromy.CoupledPullback.Root`, `Monodromy.CoupledPullback.lowerCovering`, `Monodromy.CoupledPullback.lowerProjection`, `Monodromy.CoupledPullback.upperCovering`, `Monodromy.CoupledPullback.upperProjection`, `Monodromy.NestedRestricted.baseSet`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.program`, `Monodromy.ReversibleNativeTuring.size_nonzero`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.size`.
--
--   Proof elaboration dependencies: `Monodromy.CoupledContinuation.Driver`, `Monodromy.CoupledContinuation.Driver.restrictedPath`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.runDriver`, `Monodromy.CoupledContinuation.Program.runDriver_of_reaches`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.CoupledContinuation.execute`, `Monodromy.CoupledContinuation.intermediateCurve`, `Monodromy.CoupledContinuation.intermediateCurve_actual_lift`, `Monodromy.CoupledContinuation.intermediatePath`, `Monodromy.CoupledContinuation.restrictedBase`, `Monodromy.CoupledContinuation.restrictedState`, `Monodromy.CoupledContinuation.restrictedState_over_base`, `Monodromy.CoupledContinuation.restrictedTrajectory`, `Monodromy.CoupledContinuation.restrictedTrajectory_actual_lift`, `Monodromy.CoupledContinuation.restrictedTrajectory_end`, `Monodromy.CoupledPullback.Base`, `Monodromy.CoupledPullback.Lower`, `Monodromy.CoupledPullback.Point`, `Monodromy.CoupledPullback.Punctured`, `Monodromy.CoupledPullback.Root`, `Monodromy.CoupledPullback.lowerCovering`, `Monodromy.CoupledPullback.lowerProjection`, `Monodromy.CoupledPullback.upperCovering`, `Monodromy.CoupledPullback.upperProjection`, `Monodromy.NestedRestricted.baseSet`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleNativeTuring.Related`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.program`, `Monodromy.ReversibleNativeTuring.respects`, `Monodromy.ReversibleNativeTuring.size_nonzero`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.size`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/FormalCompilation.lean (file SHA-256 c07335814044367fc4605d1e494fe82a30c684f754d58d55aaa7514b94c37122):
--   Monodromy.ReversibleNativeTuring.finite_run_actual_lifts at L1576-L1597 [UTF-8 84917:86361].

module
public import Definitions.Def_Monodromy_FormalCompilation
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
public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
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
open Monodromy.ReversibleNativeTuring
open Turing CoupledContinuation ReversibleTuring
variable (a q : ℕ) [NeZero a] [NeZero q]

theorem Monodromy.ReversibleNativeTuring.finite_run_actual_lifts (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (history : ℕ)
    (run : StateTransition.Reaches (TM0.step machine) first last) :
    ∃ finalHistory, ∃ count : ℕ,
      let initial := iota a q machine first history
      let driver := (program a q machine).runDriver count initial
      intermediateCurve driver initial =
        CoupledPullback.lowerCovering.liftPath driver.restrictedPath
          (CoupledPullback.upperProjection (restrictedState initial))
          (driver.restrictedPath.source.trans (restrictedState_over_base initial).symm) ∧
      restrictedTrajectory driver initial =
        CoupledPullback.upperCovering.liftPath (intermediatePath driver initial) (restrictedState initial)
          (intermediatePath driver initial).source ∧
      restrictedTrajectory driver initial 1 = restrictedState (iota a q machine last finalHistory) := by sorry
