-- Prove2me | Theorems.Thm_MasulloRH_logDeriv_analytic_right
-- name    : MasulloRH.logDeriv_analytic_right
-- status  : Open
-- author  : @davidloeffler
-- created : 2026-11-20T19:21:36.238361+00:00
-- url     : https://prove2.me/theorems/baeca5a2-54b5-48ae-96f2-4c9f57a316ca
-- title:
--   §1.4.5 — Holomorphy of the zeta logarithmic derivative right of the critical line
-- statement:
--   For every complex $s$ with $\operatorname{Re}(s)>1/2$ and $s\ne1$, the logarithmic derivative $\zeta'/\zeta$ is analytic at $s$. This is the $F=\mathbf Q$, trivial-character specialization of the claimed consequence in §1.4.5, pp.29–30, after removing the shift by $1/2$. This is an open proof obligation, not an assumed fact. Establishing it by Masullo's argument requires the trace formula and the limiting/analytic-continuation argument; those are not hypotheses of this statement.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, draft linked 20 November 2026, §1.4.5, pp.29–30; Riemann zeta specialization (F=Q, trivial Hecke character). https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.Basic
set_option autoImplicit false

namespace MasulloRH

theorem logDeriv_analytic_right (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ => deriv riemannZeta z / riemannZeta z) s := by sorry

end MasulloRH
