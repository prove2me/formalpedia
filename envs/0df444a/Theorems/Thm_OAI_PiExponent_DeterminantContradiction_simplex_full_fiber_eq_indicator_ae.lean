-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_full_fiber_eq_indicator_ae
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_full_fiber_eq_indicator_ae
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:02:00.838273+00:00
-- url     : https://prove2.me/theorems/4fe84908-2670-4546-9dc5-d3727df4bc71
-- title:
--   Identify full fibers almost everywhere
-- statement:
--   For almost every real parameter, the full fiber volume equals the interval-indicated slice volume; the only possible exceptional parameter is the null endpoint `t = 0`.

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_full_fiber_eq_indicator_ae (n : Nat) (T : Real) (hT : 0 < T) : (fun t : Real => Set.indicator (Set.Ioo (0 : Real) T) (fun u : Real => MeasureTheory.volume {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - u}) t) =ᵐ[MeasureTheory.volume] (fun t : Real => MeasureTheory.volume {y : Fin n → Real | 0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t}) := by sorry
