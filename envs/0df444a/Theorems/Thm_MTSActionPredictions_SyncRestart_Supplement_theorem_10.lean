-- Prove2me | Theorems.Thm_MTSActionPredictions_SyncRestart_Supplement_theorem_10
-- name    : MTSActionPredictions.SyncRestart.Supplement.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:30:27.459224+00:00
-- url     : https://prove2.me/theorems/1032f429-955b-4826-a89c-a0b63337488f
-- title:
--   Theorem 10 ([BBN07]) — strictly $O(\log k)$-competitive fractional weighted paging from every integral initial cache
-- statement:
--   There is a universal constant $C>0$ with the following property. For every number of pages $n$, every cache size $k$ with $1\le k\le n$ and all page weights $w_p\ge0$, there is a deterministic online algorithm for fractional weighted paging such that, from every integral initial cache $x_0$ of size $k$ and on every finite request sequence $p_1,\dots,p_T$:
--
--   1. the algorithm outputs fractional configurations $x_1,\dots,x_T$ of size $k$ with $x_t(p_t)=1$, and
--   2. for every fractional offline solution $y_0=x_0,y_1,\dots,y_T$ serving the requests,
--   $$\sum_{t=1}^T d(x_{t-1},x_t)\le C\,(1+\ln k)\sum_{t=1}^T d(y_{t-1},y_t),\qquad d(x,x')=\sum_p w_p|x_p-x'_p|.$$
--
--   Both loading and eviction are charged, and there is no additive constant. The paper uses this result, attributed to Bansal, Buchbinder and Naor, to build the short-sequence algorithm for weighted paging.
--
--   Differences from the source:
--   - reading: strictly O(log k)-competitive → strictly C(1 + ln k)-competitive with one universal C > 0; reason: at k = 1 the literal C·log k = 0 cannot bound a positive cost; 1 + ln k is the standard reading and agrees up to a factor 2 for k ≥ 2
--   - reading: an online algorithm for fractional weighted paging → a deterministic online rule, which may depend on n, k and the weights; reason: the fractional algorithm of BBN07 is deterministic, and a randomized fractional algorithm can be derandomized by averaging configurations; the deterministic reading is the stronger one
--   - encoding: cache size k ≤ n → 1 ≤ k ≤ n; reason: with k = 0 no configuration can serve any request
--   - encoding: competitive against every offline solution → against every fractional sequence from the same initial cache serving the requests; the algorithm’s outputs are required to be feasible; reason: the offline solutions of fractional paging are fractional configurations; the source’s MTS charges ∞ to infeasible configurations
-- source:
--   Júlia Baligács, Christian Coester, Alexa Tudose, STOC 2027 submission #1248 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1248.pdf; Theorem 10, PDF p. 10 / printed p. 9, with the preceding paragraph; model §4, PDF p. 9 / printed p. 8

import Definitions.Def_MTSActionPredictions_SyncRestart_Supplement_Paging

namespace MTSActionPredictions.SyncRestart.Supplement

/-- Theorem 10 ([BBN07]), PDF 10 / printed 9: there is a universal constant `C` such that for every
number of pages `n`, every cache size `1 ≤ k ≤ n` and all page weights `w_p ≥ 0`, some deterministic
online algorithm for fractional weighted paging is strictly `C (1 + ln k)`-competitive from every
integral initial cache: on every request sequence it outputs feasible fractional configurations, and
its total movement cost (loading and eviction) is at most `C (1 + ln k)` times that of every
feasible fractional offline solution from the same initial cache, with no additive term. -/
theorem theorem_10 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ), 1 ≤ k → k ≤ n → ∀ w : Fin n → ℝ, (∀ p, 0 ≤ w p) →
      ∃ A : PagingRule n, ∀ x₀ : Fin n → ℝ, IsIntegralCache k x₀ → ∀ q : List (Fin n),
        ServesRequests k q (pagingTraj A x₀ q) ∧
        ∀ Y : ℕ → Fin n → ℝ, Y 0 = x₀ → ServesRequests k q Y →
          pagingCost w q.length (pagingTraj A x₀ q) ≤
            C * (1 + Real.log k) * pagingCost w q.length Y := by sorry

end MTSActionPredictions.SyncRestart.Supplement
