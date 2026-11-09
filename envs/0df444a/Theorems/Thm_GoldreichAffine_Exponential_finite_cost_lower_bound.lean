-- Prove2me | Theorems.Thm_GoldreichAffine_Exponential_finite_cost_lower_bound
-- name    : GoldreichAffine.Exponential.finite_cost_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:33.897089+00:00
-- url     : https://prove2.me/theorems/0d7f564f-9fe7-40d3-9844-b5505eeb7cc5
-- title:
--   Lemma 3 — finite-parameter optimal cost lower bound
-- statement:
--   Fix positive integers $n,m,b$ with $b\le n$, $0\le w\le n$ and an arbitrary $b$-bit predicate $M$. Let $C^\star$ be the minimum of the exact idealized cost in (1)–(6), using every feasible guess and real-valued count vector. For each feasible reduced pair $(n′,w′)$, let $\mu_r$ be its expected class capacity and let $\Phi$ be the pairing envelope from Lemma 2. Then
--   $$\log_2 C^\star\ge\min_{(n′,w′)\mathrm{\ feasible}}\left\{\log_2\frac{\binom n w}{\binom{n′}{w′}}+n′-\max_{\substack{0\le k_r\le\mu_r\\\sum_r k_r\le n′}}\sum_r k_r\log_2(1+2\Phi(n′,w′,b-r))\right\}.$$
--   Equivalently, defining $g(n′,w′)=\log_2[\binom n w/\binom{n′}{w′}]$ and $v(n′,w′)$ as the displayed count-vector maximum,
--   $$\log_2 C^\star\ge\min_{(n′,w′)\mathrm{\ feasible}}\{g(n′,w′)+n′-v(n′,w′)\}.$$
--   All sums and optimizations include only feasible overlap classes. No logarithmic-arity restriction is imposed. This is the finite-parameter lower bound on which the exponential-cost implication rests.
--
--   Differences from the source:
--   - encoding: a feasible global guess (R,u) → its feasible reduced parameters (n′,w′); reason: every pair with n′≤n, w′≤n′, w′≤w and w−w′≤n−n′ is realizable, and the source probabilities and costs depend only on this pair
--   - encoding: finite real costs, maxima and minima → nonnegative extended costs and extended logarithms and extrema; reason: on the feasible source domain the optimal cost lies in [1,2^n], all benefit maxima are finite and attained, and the extended quantities equal the source real values; no real infimum default or conversion of infinity to zero is used
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, STOC 2027 submission #579 (October 2026), p. 15 (PDF p. 16), Lemma 3, Eq. (13) and its equivalent formulation; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/579.pdf

import Definitions.Def_GoldreichAffine_Exponential_TransferBenefit
open scoped NNReal ENNReal
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential

/-- Lemma 3, printed p.15 / PDF p.16: exact finite-parameter bound (13). -/
theorem finite_cost_lower_bound {n m b w : ℕ} (M : Predicate b)
    (hn : 0 < n) (hm : 0 < m) (hb : 0 < b) (hbn : b ≤ n) (hw : w ≤ n) :
    lowerCertificate M n m w ≤ logCost (optimalCost M n m w) := by sorry

end GoldreichAffine.Exponential
