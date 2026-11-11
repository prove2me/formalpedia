-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_eq_2_2
-- name    : FracColorLocal.KrFree.eq_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:12:12.578328+00:00
-- url     : https://prove2.me/theorems/cbb16397-1260-40a2-81f5-b1fe1f29f2c6
-- title:
--   (2.2) — Shearer's differential identity d(d−1)f′(d) + (d+1)f(d) = 1 for d > 0
-- statement:
--   Let $f$ be Shearer's function, $f(d)=(d\log d-d+1)/(d-1)^2$ for $d>0$, $d\ne1$, $f(1)=1/2$. For every $d>0$,
--
--   $$d(d-1)f'(d)+(d+1)f(d)=1 .$$
--
--   The identity is the differential equation that makes Shearer's bound work: it is exactly the condition under which the deletion step of the triangle-free argument loses nothing (§2.1). Appendix A proves it by differentiating the explicit formula for $d\ne1$ and by continuity at $d=1$.
--
--   Differences from the source:
--   - reading: identity (2.2) stated without a domain in §2.1 → for every real $d>0$; reason: Appendix A proves it for $d\ne1$ and at $d=1$ by continuity, and $f'(0)$ does not exist ($-f'(d)\to\infty$ as $d\downarrow0$).
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 7 (PDF 8), §2.1, (2.2); p. 48 (PDF 49), Appendix A

import Mathlib
import Definitions.Def_FracColorLocal_KrFree_Shearer

namespace FracColorLocal.KrFree

/-- (2.2) / Appendix A: Shearer's function satisfies `d(d-1) f'(d) + (d+1) f(d) = 1` for `d > 0`. -/
theorem eq_2_2 (d : ℝ) (hd : 0 < d) :
    d * (d - 1) * deriv shearerF d + (d + 1) * shearerF d = 1 := by sorry

end FracColorLocal.KrFree
