-- Prove2me | Theorems.Thm_Kyprianou_Ch02_nonnegLaplaceIntegralTendstoV1
-- name    : Kyprianou.Ch02.nonnegLaplaceIntegralTendstoV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:02:24.004322+00:00
-- url     : https://prove2.me/theorems/60445397-a491-4a7d-9deb-73fcc1d5ed28
-- title:
--   Bounded nonnegative Laplace expectations converge under almost sure convergence
-- statement:
--   Use continuity and dominated convergence with the uniform integrable bound one.
-- source:
--   Kyprianou (2006), Exercise 2.8, independence of Jordan variation components.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.nonnegLaplaceIntegralTendstoV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ × ℝ) (f : Ω → ℝ × ℝ)
    (hm : ∀ n, AEMeasurable (F n) P)
    (hn : ∀ n, ∀ᵐ ω ∂P, 0 ≤ (F n ω).1 ∧ 0 ≤ (F n ω).2)
    (ht : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (nhds (f ω)))
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Tendsto (fun n => ∫ ω, Real.exp (-(u*(F n ω).1+v*(F n ω).2)) ∂P) atTop
      (nhds (∫ ω, Real.exp (-(u*(f ω).1+v*(f ω).2)) ∂P)) := by sorry
