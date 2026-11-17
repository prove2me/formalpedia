-- Prove2me | Theorems.Thm_N25_etaAnalytic25_normalized_hasSum
-- name    : N25.etaAnalytic25_normalized_hasSum
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:43.78225+00:00
-- url     : https://prove2.me/theorems/6152b225-e93f-4a57-9f2f-34392b90ef09
-- title:
--   The normalized eta residue function has the prescribed power series
-- statement:
--   Let $0<g<25$, let $\tau$ lie in the upper half-plane, put $q=e^{2\pi i\tau}$, and let $a_n$ be the coefficients of the integral residue series attached to $g$. Then
--
--   $$\sum_{n\ge0}a_nq^n=\frac{E_g(\tau)}{e^{\pi iB_2(g/25)25\tau}}.$$
--
--   This realizes the normalized analytic eta factor by the explicit integral power series.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.etaAnalytic25_normalized_hasSum
    (g : ℕ) (hg : 0 < g) (hg25 : g < 25) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => ((PowerSeries.coeff n (etaResidueSeries25 g) : ℤ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ n)
      (etaAnalytic25 g τ / Complex.exp (Real.pi * Complex.I *
        (((g : ℂ) / 25) ^ 2 - (g : ℂ) / 25 + 1 / 6) * (25 * (τ : ℂ)))) := by sorry
