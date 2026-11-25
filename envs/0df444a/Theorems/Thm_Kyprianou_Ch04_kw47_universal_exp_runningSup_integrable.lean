-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_universal_exp_runningSup_integrable
-- name    : Kyprianou.Ch04.kw47_universal_exp_runningSup_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:10:05.665551+00:00
-- url     : https://prove2.me/theorems/887dfb4d-3f22-5732-be83-b349caf3cdfa
-- title:
--   Finite-horizon exponential running-supremum integrability for every spectrally negative Lévy process
-- statement:
--   For every spectrally negative Lévy process, every nonnegative alpha and finite horizon T, exp(alpha runningSup(X,T)) is integrable under the original path probability measure. Split into the exhaustive BV/UBV alternatives: the bounded-variation case follows from the Proved deterministic linear-drift cap and the UBV case follows from the Proved all-parameter finite-horizon exponential maximum result. This combines existing exact same-space results without new stochastic assumptions. It furnishes a single integrable envelope for every finite Esscher product-grid sum.
-- source:
--   Kyprianou (2006), Exercise 4.7, p.108 and solutions pp.320–321; reuse of published Avram finite-horizon exponential supremum estimate.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_BV_exp_runningSup_integrable
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_alltheta_finitehorizon_runningSup_exp_integrable
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exponential running-supremum integrability holds for all
spectrally negative Lévy processes, independently of path variation. -/

theorem Kyprianou.Ch04.kw47_universal_exp_runningSup_integrable
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha) (T : NNReal) :
    Integrable (fun w : Ω => Real.exp (alpha * runningSup L T w)) P := by sorry
