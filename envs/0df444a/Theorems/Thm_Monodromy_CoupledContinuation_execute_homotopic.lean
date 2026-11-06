-- Prove2me | Theorems.Thm_Monodromy_CoupledContinuation_execute_homotopic
-- name    : Monodromy.CoupledContinuation.execute_homotopic
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:36:31.415574+00:00
-- url     : https://prove2.me/theorems/d789cf46-769f-498a-8211-7b2e8eb789ca
-- title:
--   Admissible Based Homotopies Preserve Complete Native Execution
-- statement:
--   For any two coupled drivers whose restricted based paths are homotopic with endpoints fixed, and every state s in the coupled fiber, their actual lifted executions have the same complete endpoint state: execute(first,s)=execute(second,s). The homotopy is taken in the restricted base used by the matching lower and upper coverings.
--
--   Statement dependencies: `Monodromy.CoupledContinuation.Driver`, `Monodromy.CoupledContinuation.Driver.restrictedPath`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.execute`, `Monodromy.CoupledContinuation.restrictedBase`, `Monodromy.CoupledPullback.Base`, `Monodromy.CoupledPullback.Punctured`, `Monodromy.NestedRestricted.baseSet`.
--
--   Original proof dependencies: `Monodromy.CoupledContinuation.Driver`, `Monodromy.CoupledContinuation.Driver.restrictedPath`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.execute`, `Monodromy.CoupledContinuation.forgetPoint`, `Monodromy.CoupledContinuation.intermediateCurve`, `Monodromy.CoupledContinuation.intermediateCurve_actual_lift`, `Monodromy.CoupledContinuation.intermediatePath`, `Monodromy.CoupledContinuation.restrictedBase`, `Monodromy.CoupledContinuation.restrictedState`, `Monodromy.CoupledContinuation.restrictedState_over_base`, `Monodromy.CoupledContinuation.restrictedTrajectory`, `Monodromy.CoupledContinuation.restrictedTrajectory_actual_lift`, `Monodromy.CoupledPullback.Base`, `Monodromy.CoupledPullback.Lower`, `Monodromy.CoupledPullback.Point`, `Monodromy.CoupledPullback.Punctured`, `Monodromy.CoupledPullback.Root`, `Monodromy.CoupledPullback.lowerCovering`, `Monodromy.CoupledPullback.lowerProjection`, `Monodromy.CoupledPullback.upperCovering`, `Monodromy.CoupledPullback.upperProjection`, `Monodromy.NestedRestricted.baseSet`.
--
--   Statement elaboration dependencies: `Monodromy.CoupledContinuation.Driver`, `Monodromy.CoupledContinuation.Driver.restrictedPath`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.execute`, `Monodromy.CoupledContinuation.restrictedBase`, `Monodromy.CoupledPullback.Base`, `Monodromy.CoupledPullback.Punctured`, `Monodromy.NestedRestricted.baseSet`.
--
--   Proof elaboration dependencies: `Monodromy.CoupledContinuation.Driver`, `Monodromy.CoupledContinuation.Driver.restrictedPath`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.execute`, `Monodromy.CoupledContinuation.forgetPoint`, `Monodromy.CoupledContinuation.intermediateCurve`, `Monodromy.CoupledContinuation.intermediateCurve_actual_lift`, `Monodromy.CoupledContinuation.intermediatePath`, `Monodromy.CoupledContinuation.restrictedBase`, `Monodromy.CoupledContinuation.restrictedState`, `Monodromy.CoupledContinuation.restrictedState_over_base`, `Monodromy.CoupledContinuation.restrictedTrajectory`, `Monodromy.CoupledContinuation.restrictedTrajectory_actual_lift`, `Monodromy.CoupledPullback.Base`, `Monodromy.CoupledPullback.Lower`, `Monodromy.CoupledPullback.Point`, `Monodromy.CoupledPullback.Punctured`, `Monodromy.CoupledPullback.Root`, `Monodromy.CoupledPullback.lowerCovering`, `Monodromy.CoupledPullback.lowerProjection`, `Monodromy.CoupledPullback.upperCovering`, `Monodromy.CoupledPullback.upperProjection`, `Monodromy.NestedRestricted.baseSet`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Continuation.lean (file SHA-256 c41996cad30503403fe284de8929124f849aa5fd0aaba5433e5e0d4d36fec912):
--   Monodromy.CoupledContinuation.execute_homotopic at L1767-L1785 [UTF-8 88114:89404].

module
public import Definitions.Def_Monodromy_Continuation
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
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Monodromy
open Monodromy.CoupledContinuation

theorem Monodromy.CoupledContinuation.execute_homotopic (first second : Driver)
    (deformation : first.restrictedPath.Homotopic second.restrictedPath) (state : Memory) :
    execute first state = execute second state := by sorry
