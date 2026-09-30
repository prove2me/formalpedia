-- Prove2me | Theorems.Thm_KellyStochasticNetworks_reversible_iff_detailed_balance
-- name    : KellyStochasticNetworks.reversible_iff_detailed_balance
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T05:48:14.076141+00:00
-- url     : https://prove2.me/theorems/a4ee167b-c48b-4e37-b90d-5582d3bb34a7
-- title:
--   Reversibility is exactly detailed balance
-- statement:
--   Let $\pi$ be a strictly positive collection of numbers on a state space $S$ and let $q$ be a
--   matrix of transition rates. Write
--   $$q'(j,k) = \frac{\pi(k)\,q(k,j)}{\pi(j)}$$
--   for the rates of the time-reversed process of Proposition 1.1. Then
--   $$q' = q \quad \Longleftrightarrow \quad \pi(j)\,q(j,k) = \pi(k)\,q(k,j) \ \text{ for all } j,k \in S.$$
--
--   In words: a stationary Markov process is **reversible** — indistinguishable from itself run
--   backwards in time — precisely when its equilibrium distribution and its rates satisfy the
--   detailed balance equations (1.4). This equivalence is the reason the book looks for
--   equilibrium distributions by solving detailed balance: a solution of those equations is not
--   merely an equilibrium distribution, it is a certificate of reversibility.
--
--   **Formalization Note** Equality of rate matrices is equality of the two functions of two
--   arguments, and the hypothesis that $\pi$ is strictly positive is needed in both directions
--   because $\pi(j)$ appears in a denominator.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 17 (PDF p. 25): 'If the reversed process has the same transition rates as the original process we call the process reversible. In order for this to hold, i.e. to have q(j,k) = q'(j,k), we need the following detailed balance equations to be satisfied', equation (1.4). sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem reversible_iff_detailed_balance {S : Type*} (π : S → ℝ) (q : S → S → ℝ)
    (hπ : ∀ j, 0 < π j) : reversedRates π q = q ↔ DetailedBalance π q := by sorry

end KellyStochasticNetworks
