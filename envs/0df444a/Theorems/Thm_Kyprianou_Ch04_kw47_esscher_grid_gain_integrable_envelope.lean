-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_gain_integrable_envelope
-- name    : Kyprianou.Ch04.kw47_esscher_grid_gain_integrable_envelope
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T20:19:03.501027+00:00
-- url     : https://prove2.me/theorems/1fc4b723-995c-535b-989e-84f24c02c3b7
-- title:
--   Integrable mesh-uniform dominating envelope for Esscher product grids
-- statement:
--   For any spectrally negative Lévy process, nonnegative alpha and horizon T, the random variable 4 exp(alpha runningSup(X,T)+|psi(alpha)|T) exp(|psi(alpha)|T) is integrable. This is a deterministic positive scalar multiple of exp(alpha runningSup(X,T)), whose integrability for all path variation regimes is already Proved. This is exactly the common envelope dominating every finite Kella–Whitt Esscher grid sum up to T.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.7, p.108 and solution pp.320–321, dominated convergence for the true martingale.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_universal_exp_runningSup_integrable
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The mesh-independent uniform dominating envelope for exact
Kella-Whitt Esscher product-grid sums is integrable. -/

theorem Kyprianou.Ch04.kw47_esscher_grid_gain_integrable_envelope
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha) (T : NNReal) :
    Integrable (fun w : Ω =>
      4 * Real.exp (alpha * runningSup L T w +
          |L.ψ alpha| * (T : Real)) *
        Real.exp (|L.ψ alpha| * (T : Real))) P := by sorry
