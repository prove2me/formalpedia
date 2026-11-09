-- Prove2me | Theorems.Thm_IdentityTesting39_ExactRadius_eq_8_min_variance
-- name    : IdentityTesting39.ExactRadius.eq_8_min_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:01.985681+00:00
-- url     : https://prove2.me/theorems/aead4bb1-d290-4b6c-91dd-b7c9edbadee1
-- title:
--   §5, (8) — attained minimum variance at fixed deficit and excess
-- statement:
--   Let $q>0$ and let $\mu$ be a nonnegative probability law with a finite second moment. Write $r=\mathbb EU$, $d=\mathbb E(q-U)_+$ and $e=\mathbb E(U-q)_+$. Then $r=q-d+e$ and the variance is at least
--
--   $$v=\begin{cases}4de&d+e\le q,\\r^2d/(q-d)&d+e\ge q,\ d<q.\end{cases}$$
--
--   The explicit two-point law in (8) has these same moments and variance exactly $v$, so the minimum is attained. The local law puts masses $d/(d+e),e/(d+e)$ at $q-(d+e),q+(d+e)$. The sparse law puts positive mass $(q-d)/q$ at $rq/(q-d)$ and its remaining mass at zero. At $d=0$ use the deterministic value $q+e$; at $d=q$ one has $r=e=0$ and uses zero. The formulas agree where $d+e=q$, and always $v\ge4de$. These are nonnegative laws, with no artificial upper support restriction.
--
--   Differences from the source:
--   - encoding: a nonnegative scalar law with its mean and variance → a probability measure almost surely nonnegative with integrable square; reason: this makes the finite-moment convention explicit and prevents the integral default
--   - encoding: endpoint degeneracies interpreted directly → explicit Dirac laws and v=0 when d=0 or d=q; reason: these are precisely the endpoints specified in Appendix C.1
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.6, §5, display (8); Appendix C.1, p.18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_ScalarMoments

open MeasureTheory

namespace IdentityTesting39.ExactRadius

/-- §5, (8), printed p.6 / PDF p.7, with the endpoints in Appendix C.1, p.18. -/
theorem eq_8_min_variance (q : ℝ) (hq : 0 < q) (μ : Measure ℝ)
    (hμ : NonnegativeSecondMomentLaw μ) :
    let r := scalarMean μ
    let d := scalarDeficit q μ
    let e := scalarExcess q μ
    let v := minimumVariance q r d e
    r = q-d+e ∧ 4*d*e ≤ v ∧ v ≤ scalarVariance μ ∧
    (d+e ≤ q → v = 4*d*e) ∧
    (q ≤ d+e → d < q → v = r^2*d/(q-d)) ∧
    (d = q → r = 0 ∧ e = 0 ∧ v = 0) ∧
    (d+e = q → d < q → 4*d*e = r^2*d/(q-d)) ∧
    NonnegativeSecondMomentLaw (extremalLaw q r d e) ∧
    scalarMean (extremalLaw q r d e) = r ∧
    scalarDeficit q (extremalLaw q r d e) = d ∧
    scalarExcess q (extremalLaw q r d e) = e ∧
    scalarVariance (extremalLaw q r d e) = v := by sorry

end IdentityTesting39.ExactRadius
