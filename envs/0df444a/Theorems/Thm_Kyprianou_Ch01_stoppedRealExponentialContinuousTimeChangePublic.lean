-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stoppedRealExponentialContinuousTimeChangePublic
-- name    : Kyprianou.Ch01.stoppedRealExponentialContinuousTimeChangePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:41:24.90155+00:00
-- url     : https://prove2.me/theorems/173cf734-ff0c-4a57-b152-93bb9b478ece
-- title:
--   Stopped real exponential converges under convergent stopping times on a continuous path
-- statement:
--   If a real path indexed by nonnegative time is continuous, and a sequence of finite nonnegative stopping times converges to a finite time tau, then the exponential of theta times the path value minus q times the stopping time converges to the corresponding exponential evaluated at tau. This deterministic continuous mapping lemma isolates the analytic composition step needed by Brownian first-passage grid convergence.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10(ii), continuity of stopped exponential at first passage.

import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.FunProp
open Filter
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stoppedRealExponentialContinuousTimeChangePublic
    (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (theta q : ℝ)
    (t : ℕ → ℝ≥0) (tau : ℝ≥0)
    (ht : Tendsto t atTop (nhds tau)) :
    Tendsto
      (fun n : ℕ =>
        Real.exp (theta * f (t n) - q * ((t n) : ℝ)))
      atTop
      (nhds (Real.exp (theta * f tau - q * (tau : ℝ)))) := by sorry
