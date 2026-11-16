-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_Supplement_joint_monomer_dimer_covariance
-- name    : MatchingNearLinear.Glauber.Supplement.joint_monomer_dimer_covariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:05:28.477822+00:00
-- url     : https://prove2.me/theorems/74c6bc41-4596-44be-aec9-a4ebe0f2abe7
-- title:
--   Theorem A.1 — Covariance bound for monomer and dimer indicators
-- statement:
--   Let $\eta(x)=\big(\sqrt{1+3x}+6\sqrt x\big)^2$.
--
--   1. For every $\lambda_{\max}>0$, every labeled finite simple graph $H$ with activities $0<\lambda_e\le\lambda_{\max}$ and unit monomer weights, $\mu=\mu_{H,\lambda}$ and the joint vector $Z=(X,J)$ of dimer and monomer indicators, including mixed covariances,
--   $$\operatorname{Cov}(Z)\ \preceq\ \eta(\lambda_{\max})\operatorname{Diag}(\mathbb EZ),\qquad \operatorname{Diag}(\mathbb EZ)=\operatorname{Diag}\big((\mu(e))_{e\in E},(\mu(v^0))_{v\in V}\big).$$
--   2. In particular, for every $a\in\mathbb R^{E}$,
--   $$\operatorname{Var}_\mu\Big(\sum_ea_eX_e\Big)\le\eta(\lambda_{\max})\sum_e\mu(e)a_e^2 .\qquad(73)$$
--   3. Both assertions hold after every feasible edge pinning $\tau$ (each edge forced present, forced absent or left free, with positive probability), for the conditional law and its conditional marginal means.
--   4. $\eta(\lambda_{\max})=1+12\sqrt{\lambda_{\max}}+O(\lambda_{\max})$ as $\lambda_{\max}\downarrow0$.
--
--   The Loewner bound is the quadratic-form inequality $a^{\mathsf T}\operatorname{Cov}(Z)a\le\eta\sum_i(\mathbb EZ_i)a_i^2$ for all $a\in\mathbb R^{E\sqcup V}$.
--
--   Differences from the source:
--
--   - encoding: after pinning, the bounds for the remaining random coordinates → the bounds for all coordinates under the conditional law; reason: pinned and other deterministic coordinates have zero covariance and nonnegative conditional means, so the two forms are equivalent
--   - encoding: Cov(Z) ⪯ η Diag(EZ) → the quadratic-form inequality for every coefficient vector (ObservableCovarianceBound); reason: the Loewner order is the quadratic-form order
--   - encoding: η(λmax) = 1 + 12√λmax + O(λmax) as λmax ↓ 0 → η(x) − 1 − 12√x = O(x) along x → 0⁺ (Asymptotics.IsBigO on nhdsWithin 0 (Ioi 0)); reason: the standard meaning of the O-symbol
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Theorem A.1 and Eq. (73), printed p. 47 (PDF p. 49); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_Supplement_JointStatistics

set_option autoImplicit false

namespace MatchingNearLinear.Glauber.Supplement

open MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/
theorem joint_monomer_dimer_covariance :
    (∀ lmax : ℝ, 0 < lmax → ∀ (n m : ℕ) (G : Input n m) (lam : Fin m → ℝ),
      ActivityBound lam lmax →
      ObservableCovarianceBound (matchingLaw G lam) (jointIndicators G) (jointConstant lmax) ∧
      (∀ a : Fin m → ℝ, variance (matchingLaw G lam) (fun M => ∑ e, a e * indicator M e) ≤
        jointConstant lmax * ∑ e, dimerMean G lam e * (a e)^2) ∧
      ∀ τ : Fin m → Option Bool, 0 < eventMass (matchingLaw G lam) indicator τ →
        ObservableCovarianceBound (edgeConditional G lam τ) (jointIndicators G)
          (jointConstant lmax) ∧
        ∀ a : Fin m → ℝ,
          variance (edgeConditional G lam τ) (fun M => ∑ e, a e * indicator M e) ≤
            jointConstant lmax * ∑ e, marginal (edgeConditional G lam τ) e * (a e)^2) ∧
    (fun x : ℝ => jointConstant x - 1 - 12 * Real.sqrt x) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun x : ℝ => x) := by sorry

end MatchingNearLinear.Glauber.Supplement
