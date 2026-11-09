-- Prove2me | Theorems.Thm_GoldreichAffine_Exponential_asymptotic_cost_upper_bound
-- name    : GoldreichAffine.Exponential.asymptotic_cost_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:30.746908+00:00
-- url     : https://prove2.me/theorems/83fae505-4615-455f-887a-47fd0dd05cde
-- title:
--   Lemma 4 — uniform asymptotic cost upper bound
-- statement:
--   Let $(M_b)_{b\ge1}$ be any predicate family and fix real $s>1$, $\gamma>0$ and $\theta\in(0,1]$. Set $m_n=\lceil n^s\rceil$, $b_n=\lceil\gamma\log_2n\rceil$ and $b′_n=\lceil\theta b_n\rceil$. For every $\varepsilon>0$ there exists an integer $N$, independent of the seed weight, such that all $n\ge N$ have valid model sizes and all $w\in\mathcal W_n$ satisfy
--   $$\log_2 C^\star(n,w;\gamma)\le[1-\theta\log_2(1+2\operatorname{adv}_{b′_n}(M_{b_n}))+\varepsilon]n.$$
--   Here $\mathcal W_n=\{0\le w\le n:|w-n/2|\le\sqrt{n\ln n}\}$ and $C^\star$ is the exact idealized minimum. The threshold may depend on $M,s,\gamma,\theta,\varepsilon$. This is precisely the source's uniform $o(1)$ assertion, with no universal numerical convergence rate. It retains the leading coefficient and supplies the upper bound relevant to necessity in the characterization.
--
--   Differences from the source:
--   - encoding: implicitly rounded integer arities and uniform o(1) → ceilings and explicit epsilon/N quantifiers with N before n and w; reason: this implements the rounding convention of section 2 and the uniform asymptotic convention of section 3.3, including all sufficiently large integers n
--   - encoding: finite real costs, maxima and minima → nonnegative extended costs and extended logarithms and extrema; reason: on the feasible source domain the optimal cost lies in [1,2^n], all benefit maxima are finite and attained, and the extended quantities equal the source real values; no real infimum default or conversion of infinity to zero is used
--   - encoding: a family indexed by positive arities → a natural-indexed family whose zero entry is ignored; reason: all uses of the predicate family are guarded by positive arity, so this adds no predicate assumption
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, STOC 2027 submission #579 (October 2026), p. 16 (PDF p. 17), Lemma 4; proof pp. 16–17 (PDF pp. 17–18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/579.pdf

import Definitions.Def_GoldreichAffine_Exponential_Asymptotic
open scoped NNReal ENNReal
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential

/-- Lemma 4, printed p.16 / PDF p.17; epsilon/N is uniform over the entire W_n. -/
theorem asymptotic_cost_upper_bound (M : PredicateFamily) (s γ θ : ℝ)
    (hs : 1 < s) (hγ : 0 < γ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ValidSize s γ n ∧ ∀ w : ℕ, TypicalWeight n w →
        logCost (asymptoticCost M s γ n w) ≤
          (((1 - θ * logTwo (1 + 2 * advantage (M (nonlinearArity γ n))
            (remainingArity θ (nonlinearArity γ n))) + ε) * (n : ℝ) : ℝ) : EReal) := by sorry

end GoldreichAffine.Exponential
