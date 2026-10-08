-- Prove2me | Theorems.Thm_LogSobolevMC_ChiSquare_theorem_3_5_iii
-- name    : LogSobolevMC.ChiSquare.theorem_3_5_iii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:02:34.267114+00:00
-- url     : https://prove2.me/theorems/aab7f752-9ffe-42dc-80bc-d35a81a4f21c
-- title:
--   Theorem 3.5 (iii) — general-chain hypercontractivity
-- statement:
--   Let $K$ be an irreducible finite-state Markov chain with positive stationary distribution $\pi$, and let $\alpha$ be its log-Sobolev constant. For every $t>0$ and finite real $q\ge2$ satisfying $q-1\le e^{2\alpha t}$,
--
--   $$
--   \|H_t f\|_q\le\|f\|_2\qquad\text{for every real function }f.
--   $$
--
--   This bound applies to every such chain, including nonreversible chains, with the exponent scale stated in the paper.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 719, Theorem 3.5 (iii), https://doi.org/10.1214/aoap/1034968224

import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

namespace LogSobolevMC.ChiSquare

theorem theorem_3_5_iii {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (hirr : MarkovMixing.Irreducible K) :
    ∀ t : ℝ, 0 < t → ∀ q : ℝ, 2 ≤ q →
      q - 1 ≤ Real.exp (2 * logSobolev K π * t) →
      ∀ f : V → ℝ, lpNorm π q (heatOp K t f) ≤ lpNorm π 2 f := by sorry

end LogSobolevMC.ChiSquare
