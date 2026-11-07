-- Prove2me | Theorems.Thm_Monodromy_ReversibleNativeTuring_native_universality
-- name    : Monodromy.ReversibleNativeTuring.native_universality
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:54:34.742498+00:00
-- url     : https://prove2.me/theorems/153a536d-9e86-4912-afd9-0225a7a1135a
-- title:
--   Complete Reversible Native Turing Universality with Actual Cover Lifts
-- statement:
--   For positive naturals a,q and every Turing machine m over Fin a and Fin q, let P,R,I be its specified forward program, reverse program and complete configuration-history encoding. All eight conclusions hold: (1) I is injective on pairs (configuration,natural history); (2) P.advance and R.advance are mutual inverses on the entire coupled fiber; (3) each successful source step x→y and each h admit one h′>h giving the specified positive native first return, forward macro value some I(y,h′), and reverse macro value I(x,h); (4) each source halt gives the defined forward macro value none; (5) for every x,y,h, existence of h′ with native terminal result I(y,h′) from I(x,h) is equivalent to source terminal result y from x; (6) native and source evaluation are defined for exactly the same encoded initial configurations; (7) they are undefined for exactly the same such configurations; and (8) every finite source run, including a zero-length or nonhalting prefix, has some final history and native advance count whose generated intermediate curve and trajectory are literally the matching lower and upper covering lifts and whose endpoint is the complete restricted encoded successor. The inverse claim concerns these compiled programs, and no growth or positive-count requirement is added to clause (8).
--
--   Statement dependencies: `Monodromy.CoupledContinuation.Driver`, `Monodromy.CoupledContinuation.Driver.restrictedPath`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.CoupledContinuation.Program.runDriver`, `Monodromy.CoupledContinuation.intermediateCurve`, `Monodromy.CoupledContinuation.intermediatePath`, `Monodromy.CoupledContinuation.restrictedBase`, `Monodromy.CoupledContinuation.restrictedState`, `Monodromy.CoupledContinuation.restrictedState_over_base`, `Monodromy.CoupledContinuation.restrictedTrajectory`, `Monodromy.CoupledPullback.Base`, `Monodromy.CoupledPullback.Lower`, `Monodromy.CoupledPullback.Point`, `Monodromy.CoupledPullback.Punctured`, `Monodromy.CoupledPullback.Root`, `Monodromy.CoupledPullback.lowerCovering`, `Monodromy.CoupledPullback.lowerProjection`, `Monodromy.CoupledPullback.upperCovering`, `Monodromy.CoupledPullback.upperProjection`, `Monodromy.NestedRestricted.baseSet`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleNativeTuring.FirstReturn`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.macroStep`, `Monodromy.ReversibleNativeTuring.program`, `Monodromy.ReversibleNativeTuring.reverseMacro`, `Monodromy.ReversibleNativeTuring.reverseProgram`, `Monodromy.ReversibleNativeTuring.size_nonzero`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.size`.
--
--   Original proof dependencies: `Monodromy.CoupledContinuation.Driver`, `Monodromy.CoupledContinuation.Driver.restrictedPath`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.CoupledContinuation.Program.runDriver`, `Monodromy.CoupledContinuation.intermediateCurve`, `Monodromy.CoupledContinuation.intermediatePath`, `Monodromy.CoupledContinuation.restrictedBase`, `Monodromy.CoupledContinuation.restrictedState`, `Monodromy.CoupledContinuation.restrictedState_over_base`, `Monodromy.CoupledContinuation.restrictedTrajectory`, `Monodromy.CoupledPullback.Base`, `Monodromy.CoupledPullback.Lower`, `Monodromy.CoupledPullback.Point`, `Monodromy.CoupledPullback.Punctured`, `Monodromy.CoupledPullback.Root`, `Monodromy.CoupledPullback.lowerCovering`, `Monodromy.CoupledPullback.lowerProjection`, `Monodromy.CoupledPullback.upperCovering`, `Monodromy.CoupledPullback.upperProjection`, `Monodromy.NestedRestricted.baseSet`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleNativeTuring.FirstReturn`, `Monodromy.ReversibleNativeTuring.divergence_iff`, `Monodromy.ReversibleNativeTuring.finite_run_actual_lifts`, `Monodromy.ReversibleNativeTuring.forward_after_reverse`, `Monodromy.ReversibleNativeTuring.halting_iff`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.iota_injective`, `Monodromy.ReversibleNativeTuring.macroStep`, `Monodromy.ReversibleNativeTuring.macroStep_iota`, `Monodromy.ReversibleNativeTuring.program`, `Monodromy.ReversibleNativeTuring.result_iff`, `Monodromy.ReversibleNativeTuring.reverseMacro`, `Monodromy.ReversibleNativeTuring.reverseProgram`, `Monodromy.ReversibleNativeTuring.reverse_after_forward`, `Monodromy.ReversibleNativeTuring.size_nonzero`, `Monodromy.ReversibleNativeTuring.step_return_pair`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.size`.
--
--   Statement elaboration dependencies: `Monodromy.CoupledContinuation.Driver`, `Monodromy.CoupledContinuation.Driver.restrictedPath`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.CoupledContinuation.Program.runDriver`, `Monodromy.CoupledContinuation.intermediateCurve`, `Monodromy.CoupledContinuation.intermediatePath`, `Monodromy.CoupledContinuation.restrictedBase`, `Monodromy.CoupledContinuation.restrictedState`, `Monodromy.CoupledContinuation.restrictedState_over_base`, `Monodromy.CoupledContinuation.restrictedTrajectory`, `Monodromy.CoupledPullback.Base`, `Monodromy.CoupledPullback.Lower`, `Monodromy.CoupledPullback.Point`, `Monodromy.CoupledPullback.Punctured`, `Monodromy.CoupledPullback.Root`, `Monodromy.CoupledPullback.lowerCovering`, `Monodromy.CoupledPullback.lowerProjection`, `Monodromy.CoupledPullback.upperCovering`, `Monodromy.CoupledPullback.upperProjection`, `Monodromy.NestedRestricted.baseSet`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleNativeTuring.FirstReturn`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.macroStep`, `Monodromy.ReversibleNativeTuring.program`, `Monodromy.ReversibleNativeTuring.reverseMacro`, `Monodromy.ReversibleNativeTuring.reverseProgram`, `Monodromy.ReversibleNativeTuring.size_nonzero`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.size`.
--
--   Proof elaboration dependencies: `Monodromy.CoupledContinuation.Driver`, `Monodromy.CoupledContinuation.Driver.restrictedPath`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.CoupledContinuation.Program.runDriver`, `Monodromy.CoupledContinuation.intermediateCurve`, `Monodromy.CoupledContinuation.intermediatePath`, `Monodromy.CoupledContinuation.restrictedBase`, `Monodromy.CoupledContinuation.restrictedState`, `Monodromy.CoupledContinuation.restrictedState_over_base`, `Monodromy.CoupledContinuation.restrictedTrajectory`, `Monodromy.CoupledPullback.Base`, `Monodromy.CoupledPullback.Lower`, `Monodromy.CoupledPullback.Point`, `Monodromy.CoupledPullback.Punctured`, `Monodromy.CoupledPullback.Root`, `Monodromy.CoupledPullback.lowerCovering`, `Monodromy.CoupledPullback.lowerProjection`, `Monodromy.CoupledPullback.upperCovering`, `Monodromy.CoupledPullback.upperProjection`, `Monodromy.NestedRestricted.baseSet`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleNativeTuring.FirstReturn`, `Monodromy.ReversibleNativeTuring.divergence_iff`, `Monodromy.ReversibleNativeTuring.finite_run_actual_lifts`, `Monodromy.ReversibleNativeTuring.forward_after_reverse`, `Monodromy.ReversibleNativeTuring.halting_iff`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.iota_injective`, `Monodromy.ReversibleNativeTuring.macroStep`, `Monodromy.ReversibleNativeTuring.macroStep_iota`, `Monodromy.ReversibleNativeTuring.program`, `Monodromy.ReversibleNativeTuring.result_iff`, `Monodromy.ReversibleNativeTuring.reverseMacro`, `Monodromy.ReversibleNativeTuring.reverseProgram`, `Monodromy.ReversibleNativeTuring.reverse_after_forward`, `Monodromy.ReversibleNativeTuring.size_nonzero`, `Monodromy.ReversibleNativeTuring.step_return_pair`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.size`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/FormalCompilation.lean (file SHA-256 c07335814044367fc4605d1e494fe82a30c684f754d58d55aaa7514b94c37122):
--   Monodromy.ReversibleNativeTuring.native_universality at L1617-L1658 [UTF-8 87510:90284].

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

theorem Monodromy.ReversibleNativeTuring.native_universality (machine : TM0.Machine (Fin a) (Fin q)) :
    let P := program a q machine
    let R := reverseProgram a q machine
    let I := iota a q machine
    Function.Injective (fun pair : TM0.Cfg (Fin a) (Fin q) × ℕ => I pair.1 pair.2) ∧
    (∀ state, R.advance (P.advance state) = state ∧ P.advance (R.advance state) = state) ∧
    (∀ first last, TM0.step machine first = some last → ∀ history,
      ∃ finalHistory, history < finalHistory ∧
        FirstReturn a q machine (I first history) (I last finalHistory) ∧
        macroStep a q machine (I first history) = Part.some (some (I last finalHistory)) ∧
        reverseMacro a q machine (I last finalHistory) = Part.some (I first history)) ∧
    (∀ state history, TM0.step machine state = none →
      macroStep a q machine (I state history) = Part.some none) ∧
    (∀ first last history,
      (∃ finalHistory, I last finalHistory ∈ P.eval (I first history)) ↔
        last ∈ StateTransition.eval (TM0.step machine) first) ∧
    (∀ state history, (P.eval (I state history)).Dom ↔
      (StateTransition.eval (TM0.step machine) state).Dom) ∧
    (∀ state history, ¬ (P.eval (I state history)).Dom ↔
      ¬ (StateTransition.eval (TM0.step machine) state).Dom) ∧
    (∀ first last history, StateTransition.Reaches (TM0.step machine) first last →
      ∃ finalHistory, ∃ count : ℕ,
        let initial := I first history
        let driver := P.runDriver count initial
        intermediateCurve driver initial =
          CoupledPullback.lowerCovering.liftPath driver.restrictedPath
            (CoupledPullback.upperProjection (restrictedState initial))
            (driver.restrictedPath.source.trans (restrictedState_over_base initial).symm) ∧
        restrictedTrajectory driver initial =
          CoupledPullback.upperCovering.liftPath (intermediatePath driver initial) (restrictedState initial)
            (intermediatePath driver initial).source ∧
        restrictedTrajectory driver initial 1 = restrictedState (I last finalHistory)) := by sorry
