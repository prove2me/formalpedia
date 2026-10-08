-- Prove2me | Theorems.Thm_LogSobolevMC_LowerBound_eq_3_6
-- name    : LogSobolevMC.LowerBound.eq_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:44.152305+00:00
-- url     : https://prove2.me/theorems/6dd41de6-3727-45b2-93f5-325f1c311a51
-- title:
--   Equation (3.6), p. 727 — interpolated heat-semigroup norm bound
-- statement:
--   Let $K$ be a finite irreducible reversible Markov chain with strictly positive stationary law $\pi$. Fix $q>2$, $t_q>0$, and $M_q$ such that $\|H_{t_q}f\|_q\le M_q\|f\|_2$ for every real function $f$. For $0\le t\le t_q$, put $p(t)=2qt_q/((2-q)t+qt_q)$. Then, for every $f$,
--
--   $$
--   \|H_t f\|_{p(t)}\le \exp\!\left(\frac{t}{t_q}\log M_q\right)\|f\|_2.
--   $$
--
--   This is the real-time form of the interpolation estimate (3.6), with $p(0)=2$ and $p(t_q)=q$. It is the input to the entropy estimate on the next milestone.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 727, §3.4, (3.6) and following displays; https://doi.org/10.1214/aoap/1034968224

import Mathlib
import Definitions.Def_LogSobolevMC_LowerBound_Setting

namespace LogSobolevMC.LowerBound

theorem eq_3_6 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (hirr : MarkovMixing.Irreducible K)
    (hrev : MarkovMixing.DetailedBalance K π)
    (q t_q M_q : ℝ) (hq : 2 < q) (ht : 0 < t_q)
    (hbound : ∀ f : V → ℝ, LogSobolevMC.ChiSquare.lpNorm π q (LogSobolevMC.ChiSquare.heatOp K t_q f) ≤ M_q * LogSobolevMC.ChiSquare.lpNorm π 2 f) :
    ∀ t : ℝ, 0 ≤ t → t ≤ t_q → ∀ f : V → ℝ,
      LogSobolevMC.ChiSquare.lpNorm π (2 * q * t_q / ((2 - q) * t + q * t_q)) (LogSobolevMC.ChiSquare.heatOp K t f) ≤
        Real.exp (t / t_q * Real.log M_q) * LogSobolevMC.ChiSquare.lpNorm π 2 f := by sorry

end LogSobolevMC.LowerBound
