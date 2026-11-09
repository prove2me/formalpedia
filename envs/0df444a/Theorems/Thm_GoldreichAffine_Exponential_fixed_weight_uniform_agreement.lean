-- Prove2me | Theorems.Thm_GoldreichAffine_Exponential_fixed_weight_uniform_agreement
-- name    : GoldreichAffine.Exponential.fixed_weight_uniform_agreement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:37.755147+00:00
-- url     : https://prove2.me/theorems/0df88081-8851-4970-84e7-551a55eb0b5e
-- title:
--   Lemma 1 — fixed-weight and uniform agreement
-- statement:
--   Let $n,b\ge1$, $b\le n$, $0\le w\le n$, and let $(n′,w′)$ be a feasible reduced guess with $n′\ge1$. Let $0\le b′\le\min(b,n′)$. For any $b$-bit predicate $M$, every residual $Q\in\mathcal R_{b′}(M)$ and every affine function $f\in\mathcal A_{b′}$,
--   $$\left|\Pr[Q(Z_{b′})=f(Z_{b′})]-q(Q,f)\right|\le\frac{b′(b′-1)}{2n′}+b′\left|\frac{w′}{n′}-\frac12\right|.$$
--   Here $Z_{b′}$ samples without replacement from a uniform $n′$-bit word of weight $w′$, whereas $q(Q,f)$ uses independent uniform input bits. The absolute value gives both directions of comparison; $b′=0$ is included. This result controls the distribution change in the asymptotic upper bound.
--
--   Differences from the source:
--   - encoding: a feasible global guess (R,u) → its feasible reduced parameters (n′,w′); reason: every pair with n′≤n, w′≤n′, w′≤w and w−w′≤n−n′ is realizable, and the source probabilities and costs depend only on this pair
--   - encoding: b′(b′−1)/(2n′) and probability differences → real arithmetic for b′−1 and finite probability sums; reason: signed real subtraction gives the same bound, including zero free inputs, and n′≥1 excludes division by zero
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, STOC 2027 submission #579 (October 2026), p. 13 (PDF p. 14), Lemma 1, Eq. (8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/579.pdf

import Definitions.Def_GoldreichAffine_Exponential_AttackModel
open scoped NNReal ENNReal
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential

/-- Lemma 1, printed p.13 / PDF p.14; signed real b'-1 preserves b'=0. -/
theorem fixed_weight_uniform_agreement {n w b np wp bp : ℕ} (M : Predicate b)
    (hn : 0 < n) (hb : 0 < b) (hbn : b ≤ n) (hw : w ≤ n)
    (hguess : FeasiblePair n w np wp) (hnp : 1 ≤ np) (hbp : bp ≤ min b np)
    (Q f : Predicate bp) (hQ : IsResidual M Q) (hf : IsAffine f) :
    |fixedAgreement np wp Q f - uniformAgreement Q f| ≤
      (bp : ℝ) * ((bp : ℝ) - 1) / (2 * (np : ℝ)) +
        (bp : ℝ) * |(wp : ℝ) / (np : ℝ) - 1 / 2| := by sorry

end GoldreichAffine.Exponential
