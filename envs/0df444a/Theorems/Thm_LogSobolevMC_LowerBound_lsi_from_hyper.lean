-- Prove2me | Theorems.Thm_LogSobolevMC_LowerBound_lsi_from_hyper
-- name    : LogSobolevMC.LowerBound.lsi_from_hyper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:36.464708+00:00
-- url     : https://prove2.me/theorems/3b81b2d3-e481-410b-a02c-faadc4fb16d2
-- title:
--   §3.4, p. 727 — entropy inequality from a heat-operator bound
-- statement:
--   Let $K$ be a finite irreducible reversible Markov chain with strictly positive stationary law $\pi$. Suppose $q>2$, $t_q>0$, and $\|H_{t_q}f\|_q\le M_q\|f\|_2$ for every real function $f$. Then every such $f$ satisfies
--
--   $$
--   \mathcal L(f)\le \frac{2q}{q-2}\left(t_q\mathcal E(f,f)+(\log M_q)\|f\|_2^2\right).
--   $$
--
--   This is the entropy inequality displayed immediately after (3.6). Together with the centering inequality (3.7), it leads to the lower bound for $\alpha$.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 727, §3.4, display after 'or'; https://doi.org/10.1214/aoap/1034968224

import Mathlib
import Definitions.Def_LogSobolevMC_LowerBound_Setting

namespace LogSobolevMC.LowerBound

theorem lsi_from_hyper {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (hirr : MarkovMixing.Irreducible K)
    (hrev : MarkovMixing.DetailedBalance K π)
    (q t_q M_q : ℝ) (hq : 2 < q) (ht : 0 < t_q)
    (hbound : ∀ f : V → ℝ, LogSobolevMC.ChiSquare.lpNorm π q (LogSobolevMC.ChiSquare.heatOp K t_q f) ≤ M_q * LogSobolevMC.ChiSquare.lpNorm π 2 f) :
    ∀ f : V → ℝ,
      LogSobolevMC.ChiSquare.entL π f ≤ 2 * q / (q - 2) *
        (t_q * LogSobolevMC.ChiSquare.dirichlet K π f f + Real.log M_q * LogSobolevMC.ChiSquare.lpNorm π 2 f ^ 2) := by sorry

end LogSobolevMC.LowerBound
