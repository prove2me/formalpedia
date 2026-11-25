-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_esscher_E_grid_horizon_bound
-- name    : Kyprianou.Ch04.kw47_esscher_E_grid_horizon_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:05:50.299168+00:00
-- url     : https://prove2.me/theorems/396f3035-bee3-5d1a-9df4-af66c03d815e
-- title:
--   Pathwise finite-horizon envelope of the Esscher exponential
-- statement:
--   For every spectrally negative Lévy path, nonnegative alpha, and 0≤r≤T, the absolute Esscher exponential exp(alpha X_r−psi(alpha)r) is bounded by exp(alpha runningSup(X,T)+|psi(alpha)|T). Use the Proved inequalities X_r≤runningSup(X,r)≤runningSup(X,T), nonnegative alpha, and elementary upper bounds on signed psi(alpha)r. This creates a single pathwise envelope for every time and all finite-grid sums, with integrability supplied by the universal exponential running-supremum theorem.
-- source:
--   Kyprianou (2006), Exercise 4.7, p.108 and solution pp. 320–321; Esscher finite-horizon path envelope.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite-horizon Esscher exponential is dominated pathwise by
the exponential of the running maximum plus a time-only factor. -/

theorem Kyprianou.Ch04.kw47_esscher_E_grid_horizon_bound
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha)
    (T r : NNReal) (hrT : r ≤ T) (w : Ω) :
    |Real.exp (alpha * L.X r w - L.ψ alpha * (r : Real))| ≤
      Real.exp (alpha * runningSup L T w +
        |L.ψ alpha| * (T : Real)) := by sorry
