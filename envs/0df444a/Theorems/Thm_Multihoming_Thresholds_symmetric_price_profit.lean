-- Prove2me | Theorems.Thm_Multihoming_Thresholds_symmetric_price_profit
-- name    : Multihoming.Thresholds.symmetric_price_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:45.427615+00:00
-- url     : https://prove2.me/theorems/2eeaefd6-dff5-4492-a522-0ac82f3f9cb9
-- title:
--   (25)–(26), PDF p. 20 (printed p. 14) — symmetric multihoming price, demand and profit
-- statement:
--   Consider the symmetric multihoming model with mismatch cost $t>0$, network-effect strength $0\le\mu<t$ and exclusive features $e$ for both goods. Let $x_i^M(p_i,p_j)$ be the multihoming demand (14), $p_i^M(p_j)$ the reaction function (15), $p^M=(t-\mu)(\mu+e)/(2t-\mu)$ the symmetric price and $\pi^M=p^M\,x_i^M(p^M,p^M)$ the symmetric profit. Then:
--
--   1. $p^M$ is a fixed point of the reaction function: $p_i^M(p^M)=p^M$;
--   2. against a rival who charges $p^M$, no price $p\in\mathbb R$ yields a larger profit along the multihoming demand: $p\,x_i^M(p,p^M)\le p^M\,x_i^M(p^M,p^M)$;
--   3. the demand at the symmetric prices is (25),
--   $$x_i^M=t\,\frac{\mu+e}{(2t-\mu)(t+\mu)};$$
--   4. the profit is (26),
--   $$\pi_i^M=\frac{t\,(t-\mu)(e+\mu)^2}{(t+\mu)(2t-\mu)^2}.$$
--
--   These closed forms are what every comparison of Proposition 2 is computed from.
--
--   **Formalization Note** Item 2 is a statement about the multihoming demand (14) only; it is not the claim that the symmetric price is a Nash equilibrium of the full pricing game (the paper's Proposition 4, which is not posed). Prices are not restricted to be nonnegative, as in the paper's first-order condition.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 20 (printed p. 14), (25), (26); with (14), (15), PDF p. 17

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model

namespace Multihoming.Thresholds

theorem symmetric_price_profit (t μ e : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) :
    reactM t μ e (pM t μ e) = pM t μ e ∧
    (∀ p : ℝ, p * demandM t μ e p (pM t μ e) ≤
      pM t μ e * demandM t μ e (pM t μ e) (pM t μ e)) ∧
    demandM t μ e (pM t μ e) (pM t μ e) = t * (μ + e) / ((2 * t - μ) * (t + μ)) ∧
    piM t μ e = t * (t - μ) * (e + μ) ^ 2 / ((t + μ) * (2 * t - μ) ^ 2) := by sorry

end Multihoming.Thresholds
