-- Prove2me | Theorems.Thm_IdentityTesting39_ExactRadius_eq_2_moment_region
-- name    : IdentityTesting39.ExactRadius.eq_2_moment_region
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:55.923818+00:00
-- url     : https://prove2.me/theorems/7ae7ffac-278e-483e-9262-161bfb4c6b58
-- title:
--   §3, (2) — exact scalar moment region
-- statement:
--   Let $q\in[0,1]$ and let $r,w,e$ be real. The law-defined moments on $[0,1]$, the convex hull of the moment curve and the explicit closed cone description agree:
--
--   $$\operatorname{Mom}_q(r,w,e,q-r+e)\iff (r,w,e)\in\operatorname{conv}\{(u,(u-q)^2,(u-q)_+):u\in[0,1]\}\iff\operatorname{Cone}_q(r,w,e).$$
--
--   Here the cone uses $s=w+2qr-q^2$, $A=e+qz$, $B=r-e-qz$, the linear inequalities $qz\le A\le z$, $0\le B\le q(1-z)$, and two closed perspective epigraphs with sum at most $s\le qr+e$. At $q=0$ it is $e=r$, $r^2\le w\le r$; $q=1$ is included. Every law-defined tuple has $d=q-r+e$. Also $(q+1)A-qz+qB=qr+e$ for every $z$. This identifies the exact scalar substrate for every program.
--
--   Differences from the source:
--   - encoding: closed perspective functions at z=0,1 → nonnegative s₁,s₂ with A²≤zs₁, B²≤(1−z)s₂, s₁+s₂≤s; reason: rotated-cone epigraphs implement the closed extensions without division
--   - encoding: moments of a random variable in [0,1] → a probability law almost surely in [0,1] and its integrals; reason: all integrands are bounded on that support; no integrability condition or instance is lost
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.4, §3, display (2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_ScalarMoments

namespace IdentityTesting39.ExactRadius

/-- §3, (2), printed p.4 / PDF p.5. -/
theorem eq_2_moment_region (q r w e : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    (ScalarMoments q r w e (q-r+e) ↔
      ![r,w,e] ∈ convexHull ℝ (momentCurve q '' Set.Icc (0 : ℝ) 1)) ∧
    (ScalarMoments q r w e (q-r+e) ↔ ScalarCone q r w e) ∧
    (∀ d, ScalarMoments q r w e d → d = q-r+e) ∧
    (∀ z : ℝ, (q+1)*(e+q*z)-q*z+q*(r-e-q*z) = q*r+e) := by sorry

end IdentityTesting39.ExactRadius
