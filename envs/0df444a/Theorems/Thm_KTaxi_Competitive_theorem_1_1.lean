-- Prove2me | Theorems.Thm_KTaxi_Competitive_theorem_1_1
-- name    : KTaxi.Competitive.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:19.453304+00:00
-- url     : https://prove2.me/theorems/8cd4054b-9146-4e47-82b1-e8474719fefd
-- title:
--   Theorem 1.1 — on every metric space, online $k$-taxi has a randomized $9^{k-1}$-competitive algorithm against adaptive online adversaries
-- statement:
--   Let $(V,d)$ be any metric space (possibly infinite and unbounded) and $k\ge1$. In the online $k$-taxi problem (hard version: each request $(r,s)$ is served by driving a taxi to $r$, paying the distance, and then carrying the passenger to $s$ for free) there is a randomized online algorithm $A$ with competitive ratio $9^{k-1}$ against adaptive online adversaries: for all initial configurations $x_0$ of the algorithm and $y_0$ of the adversary there is a constant $\beta\ge0$ such that
--   $$
--   \mathbb E[\mathrm{ALG}]\le9^{k-1}\,\mathbb E[\mathrm{ADV}]+\beta
--   $$
--   for every adaptive online adversary (which sees the algorithm's past behaviour and must serve each request itself, immediately) and every number of rounds.
--
--   It is the first competitive ratio for $k$-taxi on general metrics that depends only on $k$. The ratio is tight for $k\le2$, and with the lower bound $2^k-1$ it shows the optimal ratio against adaptive online adversaries is $2^{\Theta(k)}$.
--
--   **Formalization Note** The algorithm is existentially quantified over `OnlineAlg V k` and must be one algorithm for all initial configurations; competitiveness is `IsCompetitive` of the `Model` definition.
--
--   Differences from the source:
--   - generalization: k ≥ 2 (standing assumption, PDF p. 4: "k = 1 is trivial") → every k ≥ 1; reason: the paper excludes k = 1 only because it is trivial; the Lean statement specializes to every k ≥ 2
--   - generalization: for the given initial configuration there is an algorithm → one algorithm works for every pair of initial configurations (∃ A, ∀ x₀ y₀, ∃ β); reason: implies the version where the algorithm may depend on the start
--   - encoding: randomized online algorithm → a state machine whose step returns a discrete law (PMF) of (next state, serving taxi) from its state, its own labelled configuration and the request; reason: Theorem 1.1 is an existence statement, so a narrower algorithm class only makes it stronger; Algorithm 1 has finitely many outcomes per round
--   - generalization: the adaptive online adversary chooses each request from the algorithm's past actions → the adversary's move is any function of the full history of the algorithm's outcomes, including its internal states; reason: an action-only adversary is the special case that ignores the states, so the bound for all adversaries specializes to the paper's class
--   - generalization: the adversary moves one taxi to r to serve each request → before serving, the adversary may also move any of its taxis to a new configuration z, paying the distances travelled; reason: the paper's adversary is the special case z = current configuration; extra moves only add adversary cost
--   - generalization: both players start from the same configuration (initial potential 0, proof of Lemma 4.2, PDF p. 7) → arbitrary algorithm start x₀ and adversary start y₀; the constant β is chosen after both; reason: the case y₀ = x₀ is the paper's setting
--   - encoding: adaptive online adversary (possibly randomized) → deterministic adversaries: a function of the history; reason: a randomized adversary is a mixture of deterministic ones and E[ALG] ≤ ρE[ADV] + β is preserved by averaging
--   - encoding: E[ALG], E[ADV] over the adversary's (finite) request sequence → expected costs in ℝ≥0∞ computed on the game tree with at most T rounds (the adversary may stop earlier), for every T; reason: every finite request sequence has some length T; ℝ≥0∞ avoids undefined expectations
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (October 2026; PDF SHA-256 09242267e431f586117500ee75c63e6f203519f497d01ee4d90d6989341648ed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Theorem 1.1, PDF p. 2 (printed p. 1); proof completed at Lemma 4.8, PDF p. 14 (printed p. 13)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Model

namespace KTaxi.Competitive

/-- **Theorem 1.1** (Coester–Huang–Poon, STOC 2027 #96, PDF p. 2). On every metric space, there
is a randomized algorithm for the online k-taxi problem (hard version) with competitive ratio
`9^{k-1}` against adaptive online adversaries. Stated for every `k ≥ 1`. -/
theorem theorem_1_1 (V : Type*) [MetricSpace V] (k : ℕ) (hk : 1 ≤ k) :
    ∃ A : OnlineAlg V k, IsCompetitive A (9 ^ (k - 1)) := by sorry

end KTaxi.Competitive
