-- Prove2me | Theorems.Thm_KTaxi_Competitive_lemma_4_8
-- name    : KTaxi.Competitive.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:38.887615+00:00
-- url     : https://prove2.me/theorems/d2e4e2c3-dc95-4046-af4c-b3ac9ad8754e
-- title:
--   Lemma 4.8 — Property 4.1 for $\alpha_1=6\cdot9^{k-2}$; Algorithm 1 is $9^{k-1}$-competitive
-- statement:
--   Let $k\ge2$ and let $V$ be any metric space. Then:
--
--   1. Property 4.1 holds for Algorithm 1 with the coefficients
--   $$
--   \alpha_1=6\cdot9^{\,k-2},\qquad\alpha_m=24\cdot9^{\,k-m-1}\quad(2\le m<k),\qquad\alpha_k=3 ;
--   $$
--   2. consequently, Algorithm 1 is $9^{k-1}$-competitive against adaptive online adversaries.
--
--   Here $\alpha_1=2\sum_{m\ge2}\alpha_m$ and $\sum_m\alpha_m=9^{k-1}$; this is the bound of Theorem 1.1.
--
--   Differences from the source:
--   - generalization: the adaptive online adversary chooses each request from the algorithm's past actions → the adversary's move is any function of the full history of the algorithm's outcomes, including its internal states; reason: an action-only adversary is the special case that ignores the states, so the bound for all adversaries specializes to the paper's class
--   - generalization: the adversary moves one taxi to r to serve each request → before serving, the adversary may also move any of its taxis to a new configuration z, paying the distances travelled; reason: the paper's adversary is the special case z = current configuration; extra moves only add adversary cost
--   - generalization: both players start from the same configuration (initial potential 0, proof of Lemma 4.2, PDF p. 7) → arbitrary algorithm start x₀ and adversary start y₀; the constant β is chosen after both; reason: the case y₀ = x₀ is the paper's setting
--   - encoding: adaptive online adversary (possibly randomized) → deterministic adversaries: a function of the history; reason: a randomized adversary is a mixture of deterministic ones and E[ALG] ≤ ρE[ADV] + β is preserved by averaging
--   - encoding: E[ALG], E[ADV] over the adversary's (finite) request sequence → expected costs in ℝ≥0∞ computed on the game tree with at most T rounds (the adversary may stop earlier), for every T; reason: every finite request sequence has some length T; ℝ≥0∞ avoids undefined expectations
--   - encoding: Algorithm 1 starts from an arbitrary ordered list → it starts with the list ordered by label (state = identity permutation); reason: the labelled start x₀ is arbitrary, so every initial ordered list is realised by relabelling
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (October 2026; PDF SHA-256 09242267e431f586117500ee75c63e6f203519f497d01ee4d90d6989341648ed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Lemma 4.8 and its proof, PDF p. 14 (printed p. 13)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Model
import Definitions.Def_KTaxi_Competitive_Potential

namespace KTaxi.Competitive

/-- **Lemma 4.8** (PDF p. 13). For `k ≥ 2`, Property 4.1 holds with
`α_1 = 6 · 9^{k-2}`, `α_m = 24 · 9^{k-m-1}` for `2 ≤ m < k`, and `α_k = 3`. Consequently,
Algorithm 1 is `9^{k-1}`-competitive against adaptive online adversaries. -/
theorem lemma_4_8 {V : Type*} [MetricSpace V] {k : ℕ} [NeZero k] (hk : 2 ≤ k) :
    Property41 V k
      (fun m => if m = 1 then 6 * 9 ^ (k - 2) else if m < k then 24 * 9 ^ (k - m - 1) else 3) ∧
    IsCompetitive (algorithm1 V k) (9 ^ (k - 1)) := by sorry

end KTaxi.Competitive
