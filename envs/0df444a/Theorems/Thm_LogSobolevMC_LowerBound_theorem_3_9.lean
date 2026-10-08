-- Prove2me | Theorems.Thm_LogSobolevMC_LowerBound_theorem_3_9
-- name    : LogSobolevMC.LowerBound.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:06:55.785153+00:00
-- url     : https://prove2.me/theorems/24a8eac3-6f20-4dcf-b98f-00e5a5335b88
-- title:
--   Theorem 3.9, p. 726 — lower bound for α from a 2→q heat-operator bound
-- statement:
--   Let $K$ be a finite irreducible reversible Markov chain with strictly positive stationary distribution $\pi$. Let $\lambda$ be its variational spectral gap and $\alpha$ its log-Sobolev constant. If $2<q<\infty$, $t_q>0$, and $\|H_{t_q}f\|_q\le M_q\|f\|_2$ for every real function $f$, then
--
--   $$
--   \alpha\ge\frac{(1-2/q)\lambda}{2\bigl(\lambda t_q+\log M_q+(q-2)/q\bigr)}.
--   $$
--
--   The assertion also holds for $q=\infty$, with the $\ell^\infty$ norm, $1-2/q=1$, and $(q-2)/q=1$. It converts a single heat-operator estimate into a quantitative lower bound for the log-Sobolev constant.
--
--   **Formalization Note** Positive $t_q$ states the paper's positive-time convention. No separate bound on $M_q$ is assumed: testing the operator hypothesis on the constant function gives $M_q\ge1$.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 726, Theorem 3.9; https://doi.org/10.1214/aoap/1034968224

import Mathlib
import Definitions.Def_LogSobolevMC_LowerBound_Setting

namespace LogSobolevMC.LowerBound

theorem theorem_3_9 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (hirr : MarkovMixing.Irreducible K)
    (hrev : MarkovMixing.DetailedBalance K π) :
    (∀ (q t_q M_q : ℝ), 2 < q → 0 < t_q →
      (∀ f : V → ℝ, LogSobolevMC.ChiSquare.lpNorm π q (LogSobolevMC.ChiSquare.heatOp K t_q f) ≤ M_q * LogSobolevMC.ChiSquare.lpNorm π 2 f) →
      (1 - 2 / q) * LogSobolevMC.ChiSquare.gap K π /
        (2 * (LogSobolevMC.ChiSquare.gap K π * t_q + Real.log M_q + (q - 2) / q)) ≤ LogSobolevMC.ChiSquare.logSobolev K π) ∧
    (∀ (t_q M_q : ℝ), 0 < t_q →
      (∀ f : V → ℝ, supNorm (LogSobolevMC.ChiSquare.heatOp K t_q f) ≤ M_q * LogSobolevMC.ChiSquare.lpNorm π 2 f) →
      LogSobolevMC.ChiSquare.gap K π /
        (2 * (LogSobolevMC.ChiSquare.gap K π * t_q + Real.log M_q + 1)) ≤ LogSobolevMC.ChiSquare.logSobolev K π) := by sorry

end LogSobolevMC.LowerBound
