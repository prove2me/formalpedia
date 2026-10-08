-- Prove2me | Theorems.Thm_LogSobolevMC_ChiSquare_theorem_3_5_ii
-- name    : LogSobolevMC.ChiSquare.theorem_3_5_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:56.292715+00:00
-- url     : https://prove2.me/theorems/68b08a69-3935-45e2-99d9-a7195681a7cc
-- title:
--   Theorem 3.5 (ii) — reversible hypercontractivity
-- statement:
--   Let $K$ be an irreducible finite-state Markov chain with positive stationary distribution $\pi$, and let $\alpha$ be its log-Sobolev constant. If $(K,\pi)$ is reversible, then for every $t>0$ and finite real $q\ge2$ satisfying $q-1\le e^{4\alpha t}$,
--
--   $$
--   \|H_t f\|_q\le\|f\|_2\qquad\text{for every real function }f.
--   $$
--
--   Thus the continuous-time heat operator is contractive from $\ell^2(\pi)$ to $\ell^q(\pi)$ on the stated exponent range.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 719, Theorem 3.5 (ii), https://doi.org/10.1214/aoap/1034968224

import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

namespace LogSobolevMC.ChiSquare

theorem theorem_3_5_ii {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (hirr : MarkovMixing.Irreducible K)
    (hrev : MarkovMixing.DetailedBalance K π) :
    ∀ t : ℝ, 0 < t → ∀ q : ℝ, 2 ≤ q →
      q - 1 ≤ Real.exp (4 * logSobolev K π * t) →
      ∀ f : V → ℝ, lpNorm π q (heatOp K t f) ≤ lpNorm π 2 f := by sorry

end LogSobolevMC.ChiSquare
