-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_Supplement_joint_covariance_reduction
-- name    : MatchingNearLinear.Glauber.Supplement.joint_covariance_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:03:03.369808+00:00
-- url     : https://prove2.me/theorems/442bfe0f-185c-4500-8a96-b06e93fe3e3b
-- title:
--   Lemma A.2 — Reduction to two variance estimates
-- statement:
--   Let $G=(V,E)$ be a labeled finite simple graph with activities $\lambda_e>0$, let $\mu=\mu_{G,\lambda}$ with unit monomer weights, and let $Z=(X,J)$ be its joint vector of dimer and monomer indicators. For $\theta\in\mathbb R^E$ let $I$, $II$, $Q_1(\theta)=\sum_e\mu(e)\theta_e^2+\sum_u(\sum_{e\sim u}\mu(e)\theta_e)^2/\mu(u^0)$ and $Q_2(\theta)=\sum_e\mu(e)\theta_e^2$ be as in Appendix A. Let $\eta_1,\eta_2$ be real numbers such that for every $\theta\in\mathbb R^E$
--   $$\operatorname{Var}_\mu[I]\le\eta_1\,Q_1(\theta)\quad(74),\qquad \operatorname{Var}_\mu[II]\le\eta_2\,Q_2(\theta)\quad(75).$$
--   Then
--   $$\operatorname{Cov}(Z)\ \preceq\ \big(\sqrt{\eta_1}+\sqrt{\eta_2}\big)^2\operatorname{Diag}(\mathbb EZ),$$
--   that is, $a^{\mathsf T}\operatorname{Cov}(Z)a\le(\sqrt{\eta_1}+\sqrt{\eta_2})^2\sum_i(\mathbb EZ_i)a_i^2$ for every $a\in\mathbb R^{E\sqcup V}$.
--
--   This reduces the joint covariance bound of Theorem A.1 to the two variance bounds of Lemmas A.4 and A.6.
--
--   Differences from the source:
--
--   - generalization: activities 0 < λ_e ≤ λmax and constants η_1(λmax), η_2(λmax) → any positive activities and any real η_1, η_2; reason: the reduction uses neither the upper bound nor the form of the constants; it specializes by taking η_i = η_i(λmax)
--   - encoding: Cov(Z) ⪯ c Diag(EZ), with the auxiliary matrix A = D_E^{-1} + I_G^T D_V^{-1} I_G → the quadratic-form inequality for every coefficient vector (ObservableCovarianceBound); A is not named; reason: the Loewner order is the quadratic-form order; A is notation used only in the proof
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Lemma A.2 and Eqs. (74)–(75), printed p. 47 (PDF p. 49); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_Supplement_JointStatistics

set_option autoImplicit false

namespace MatchingNearLinear.Glauber.Supplement

open MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/
theorem joint_covariance_reduction (n m : ℕ) (G : Input n m) (lam : Fin m → ℝ)
    (hlam : ∀ e, 0 < lam e) (η1 η2 : ℝ)
    (h74 : ∀ θ : Fin m → ℝ,
      variance (matchingLaw G lam) (statI G lam θ) ≤ η1 * dimerVertexForm G lam θ)
    (h75 : ∀ θ : Fin m → ℝ,
      variance (matchingLaw G lam) (statII G lam θ) ≤ η2 * dimerForm G lam θ) :
    ObservableCovarianceBound (matchingLaw G lam) (jointIndicators G)
      ((Real.sqrt η1 + Real.sqrt η2)^2) := by sorry

end MatchingNearLinear.Glauber.Supplement
