-- Prove2me | Theorems.Thm_GoldreichAffine_Exponential_exponential_cost_characterization
-- name    : GoldreichAffine.Exponential.exponential_cost_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:38.931763+00:00
-- url     : https://prove2.me/theorems/b43bfc90-56b7-4001-9782-97c403ae188d
-- title:
--   Theorem 1 — exponential cost characterized by vanishing bit-fixing affine advantage
-- statement:
--   Let $(M_b)_{b\ge1}$ be an arbitrary family of Boolean predicates, and fix any real $s>1$. For each real $\gamma>0$, use $m_n=\lceil n^s\rceil$, $b_n=\lceil\gamma\log_2 n\rceil$ in the idealized GE-based GAA cost model (1)–(6). The following properties are equivalent:
--
--   1. For every real $\gamma>0$ and every $c$ with $0<c<2^{-(s-1)/\gamma}$ there is an integer $N$ such that, for every integer $n\ge N$ and every $w\in\mathcal W_n$,
--   $$C^\star(n,w;\gamma)>2^{cn}.$$
--   2. For every fixed real $\theta\in(0,1]$,
--   $$\lim_{b\to\infty}\operatorname{adv}_{\lceil\theta b\rceil}(M_b)=0.$$
--
--   The weight range is $\mathcal W_n=\{w\in\{0,\ldots,n\}:|w-n/2|\le\sqrt{n\ln n}\}$. The threshold in property 1 can depend on $M,s,\gamma,c$ but is independent of $w$; property 2 ranges over all positive arities, not a subsequence. Both inequalities in property 1 are strict. The equivalence is with the cost property for all admissible $(\gamma,c)$, as specified by the paragraph after Theorem 1. No balance, symmetry or nonlinearity is required, and the claim is about the modeled work factor rather than security against arbitrary algorithms.
--
--   The result makes vanishing bit-fixing affine advantage an exact criterion for the stated exponential regime of this attack model.
--
--   Differences from the source:
--   - encoding: implicitly rounded integer arities and uniform o(1) → ceilings and explicit epsilon/N quantifiers with N before n and w; reason: this implements the rounding convention of section 2 and the uniform asymptotic convention of section 3.3, including all sufficiently large integers n
--   - encoding: finite real costs, maxima and minima → nonnegative extended costs and extended logarithms and extrema; reason: on the feasible source domain the optimal cost lies in [1,2^n], all benefit maxima are finite and attained, and the extended quantities equal the source real values; no real infimum default or conversion of infinity to zero is used
--   - encoding: a feasible global guess (R,u) → its feasible reduced parameters (n′,w′); reason: every pair with n′≤n, w′≤n′, w′≤w and w−w′≤n−n′ is realizable, and the source probabilities and costs depend only on this pair
--   - encoding: a family indexed by positive arities → a natural-indexed family whose zero entry is ignored; reason: the limit uses b≥1 and the eventual cost regime has positive b_n, so no new instance or assumption is introduced
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, STOC 2027 submission #579 (October 2026), p. 8 (PDF p. 9), Theorem 1 and its immediately following quantifier-scope paragraph; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/579.pdf

import Definitions.Def_GoldreichAffine_Exponential_Asymptotic
open scoped NNReal ENNReal
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential

/-- Theorem 1, printed p.8 / PDF p.9, with the scope of the following paragraph:
    the cost property ranges over all admissible (gamma,c), uniformly in w. -/
theorem exponential_cost_characterization (M : PredicateFamily) (s : ℝ) (hs : 1 < s) :
    ExponentialCostProperty M s ↔ VanishingAdvantage M := by sorry

end GoldreichAffine.Exponential
