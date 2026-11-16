-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_Supplement_corrected_monomer_variance
-- name    : MatchingNearLinear.Glauber.Supplement.corrected_monomer_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:04:14.458236+00:00
-- url     : https://prove2.me/theorems/ce928dc9-01fe-4765-b756-fd6c94c68ecd
-- title:
--   Lemma A.6 — Corrected-monomer variance bound
-- statement:
--   Let $\lambda_{\max}>0$, let $G=(V,E)$ be a labeled finite simple graph with activities $0<\lambda_e\le\lambda_{\max}$ and $\mu=\mu_{G,\lambda}$ with unit monomer weights. For $\theta\in\mathbb R^E$ let
--   $$II=\sum_{uv\in E}\lambda_{uv}\theta_{uv}J_uJ_v-\sum_{u\in V}\frac{\sum_{e\sim u}\mu(e)\theta_e}{\mu(u^0)}J_u .$$
--   Then
--   $$\operatorname{Var}_\mu[II]\ \le\ 36\,\lambda_{\max}\sum_{e\in E}\mu(e)\theta_e^2 .$$
--   Thus (75) holds with $\eta_2(\lambda_{\max})=36\lambda_{\max}$.
--
--   Differences from the source: none.
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Lemma A.6, printed p. 50 (PDF p. 52); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_Supplement_JointStatistics

set_option autoImplicit false

namespace MatchingNearLinear.Glauber.Supplement

open MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/
theorem corrected_monomer_variance (lmax : ℝ) (hlmax : 0 < lmax) (n m : ℕ) (G : Input n m)
    (lam : Fin m → ℝ) (hlam : ActivityBound lam lmax) (θ : Fin m → ℝ) :
    variance (matchingLaw G lam) (statII G lam θ) ≤ 36 * lmax * dimerForm G lam θ := by sorry

end MatchingNearLinear.Glauber.Supplement
