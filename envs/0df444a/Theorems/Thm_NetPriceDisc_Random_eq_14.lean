-- Prove2me | Theorems.Thm_NetPriceDisc_Random_eq_14
-- name    : NetPriceDisc.Random.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:01.138278+00:00
-- url     : https://prove2.me/theorems/665dd849-33c0-478d-93bc-ff9ea9ed16d1
-- title:
--   Eq. (14) bounds, p. 20 — (n/2)((a−c)/2)² ≤ π* ≤ ½((a−c)/2)² n/(1−ρ)
-- statement:
--   Let $a>0$, $c<a$, $0<\rho<1$, and let $G$ be an $n\times n$ matrix with non-negative entries. The optimal profit $\pi^*=\sup_{p}\pi(p)$ satisfies
--   $$\frac n2\Big(\frac{a-c}{2}\Big)^2\le\pi^*\le\frac12\Big(\frac{a-c}{2}\Big)^2\frac{n}{1-\rho}.$$
--
--   So $\pi^*=\Theta(n)$ for every network, which converts a bound $o(n)$ on the regret into a bound $o(1)$ on the fractional regret.
--
--   **Formalization Note.** On p. 20 the paper writes $\pi^*(n)$ with an expectation $\mathbb E_G$ inside, but states that the bounds hold "for any network $G(n)$"; the statement is made per network, which implies the expected form. The empty network $G=0$ is included (there $\pi^*=\frac n2(\frac{a-c}2)^2$).
-- source:
--   Huang, Mani & Wang, The Value of Price Discrimination in Large Random Networks, SSRN 3368458 (EC '19 submission version), p. 20, §5.2.4, the two bounds leading to eq. (14)

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
open Matrix

namespace NetPriceDisc.Random

theorem eq_14 (a c ρ : ℝ) (ha : 0 < a) (hca : c < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j) :
    (n : ℝ) / 2 * ((a - c) / 2) ^ 2 ≤ optProfit a c ρ G ∧
      optProfit a c ρ G ≤ 1 / 2 * ((a - c) / 2) ^ 2 * ((n : ℝ) / (1 - ρ)) := by sorry

end NetPriceDisc.Random
