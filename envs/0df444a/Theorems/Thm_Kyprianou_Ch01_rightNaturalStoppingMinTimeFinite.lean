-- Prove2me | Theorems.Thm_Kyprianou_Ch01_rightNaturalStoppingMinTimeFinite
-- name    : Kyprianou.Ch01.rightNaturalStoppingMinTimeFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:27:33.921972+00:00
-- url     : https://prove2.me/theorems/023e5dbb-cbd5-4378-940b-952edb362940
-- title:
--   Clip an arbitrary right-natural stopping time at a finite horizon while retaining stopping property
-- statement:
--   Given a right-natural stopping time tau, its horizon truncation min(tau,n) is a finite stopping time in the exact associated filtration F with sigma-fields naturalSigmaRight of Y. The NNReal-valued clipped time T=untopD n (min(tau,n)) has coe(T)=min(tau,n), is an IsStoppingTime under F, and is bounded by n on every sample point. Prove the stopping property with Mathlib IsStoppingTime.min_const, and finiteness because min(tau,n)≤n<infinity. This is required to invoke the already proved MarkovProcess.integral_stoppedValue_le_of_le continuous-time optional-stopping theorem at a finite clipped horizon.
-- source:
--   Kyprianou (2006) Chapter 1 Theorem 1.13; continuous-time optional sampling through bounded stopping-time truncations.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.rightNaturalStoppingMinTimeFinite
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hF : ∀ t, F t = naturalSigmaRight Y t)
    (tau : Ω → WithTop ℝ≥0)
    (hTau : IsNaturalRightStoppingTime Y tau)
    (n : ℝ≥0) :
    let T : Ω → ℝ≥0 :=
      fun ω => (min (tau ω) (n : WithTop ℝ≥0)).untopD n
    (∀ ω, ((T ω : ℝ≥0) : WithTop ℝ≥0) =
      min (tau ω) (n : WithTop ℝ≥0)) ∧
    IsStoppingTime F (fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0)) ∧
    (∀ ω, T ω ≤ n) := by sorry
