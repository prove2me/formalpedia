-- Prove2me | Theorems.Thm_KellyStochasticNetworks_detailedBalance_implies_fullBalance
-- name    : KellyStochasticNetworks.detailedBalance_implies_fullBalance
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T05:46:05.947586+00:00
-- url     : https://prove2.me/theorems/a72311c3-b5fa-4360-bb41-a80b4b690831
-- title:
--   Detailed balance implies the equilibrium equations
-- statement:
--   Let $S$ be a state space, $q = (q(j,k))_{j,k \in S}$ a matrix of transition rates and
--   $\pi = (\pi(j))_{j \in S}$ a collection of real numbers. If $\pi$ and $q$ satisfy the detailed
--   balance equations
--   $$\pi(j)\,q(j,k) = \pi(k)\,q(k,j) \qquad \text{for all } j,k \in S,$$
--   then $\pi$ satisfies the equilibrium equations
--   $$\pi(j)\sum_{k \in S} q(j,k) = \sum_{k \in S} \pi(k)\,q(k,j) \qquad \text{for all } j \in S.$$
--
--   This is the observation, made on p. 17 of the book, that licenses the whole method of
--   Chapters 1 to 3: detailed balance is a two-term relation that can be solved by inspection,
--   full balance is not, and detailed balance is the stronger of the two. The converse fails —
--   a Markov process may have an equilibrium distribution without being reversible.
--
--   **Formalization Note** No summability hypothesis is needed: the two families being summed
--   agree term by term, so their unconditional sums agree whether or not either family is
--   summable.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 17 (PDF p. 25): 'Note that detailed balance implies the equilibrium equations (1.2), which are sometimes known as full balance.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

theorem detailedBalance_implies_fullBalance {S : Type*} (π : S → ℝ) (q : S → S → ℝ)
    (h : DetailedBalance π q) : FullBalance π q := by sorry

end KellyStochasticNetworks
