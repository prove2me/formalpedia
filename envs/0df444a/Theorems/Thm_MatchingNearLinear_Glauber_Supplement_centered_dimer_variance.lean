-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_Supplement_centered_dimer_variance
-- name    : MatchingNearLinear.Glauber.Supplement.centered_dimer_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:03:44.610323+00:00
-- url     : https://prove2.me/theorems/4d05c69f-554a-4c19-abc6-5c254f1674ce
-- title:
--   Lemma A.4 — Centered-dimer variance bound
-- statement:
--   Let $\lambda_{\max}>0$, let $G=(V,E)$ be a labeled finite simple graph with activities $0<\lambda_e\le\lambda_{\max}$ and $\mu=\mu_{G,\lambda}$ with unit monomer weights. With $Y_{uv}=X_{uv}-\lambda_{uv}J_uJ_v$, $\mu(e)=\mathbb E_\mu X_e$ and $\mu(u^0)=\mathbb P_\mu(J_u=1)$, for every $\theta\in\mathbb R^E$
--   $$\operatorname{Var}_\mu\Big[\sum_{e\in E}\theta_eY_e\Big]\ \le\ (1+3\lambda_{\max})\Big[\sum_{e\in E}\mu(e)\theta_e^2+\sum_{u\in V}\frac{\big(\sum_{e\sim u}\mu(e)\theta_e\big)^2}{\mu(u^0)}\Big].$$
--   Thus (74) holds with $\eta_1(\lambda_{\max})=1+3\lambda_{\max}$; the sum over $u$ includes isolated vertices.
--
--   Differences from the source: none.
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Lemma A.4, printed p. 49 (PDF p. 51); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_Supplement_JointStatistics

set_option autoImplicit false

namespace MatchingNearLinear.Glauber.Supplement

open MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/
theorem centered_dimer_variance (lmax : ℝ) (hlmax : 0 < lmax) (n m : ℕ) (G : Input n m)
    (lam : Fin m → ℝ) (hlam : ActivityBound lam lmax) (θ : Fin m → ℝ) :
    variance (matchingLaw G lam) (statI G lam θ) ≤
      (1 + 3 * lmax) * dimerVertexForm G lam θ := by sorry

end MatchingNearLinear.Glauber.Supplement
