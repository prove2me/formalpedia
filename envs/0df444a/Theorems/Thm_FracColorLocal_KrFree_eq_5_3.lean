-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_eq_5_3
-- name    : FracColorLocal.KrFree.eq_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:13:18.859217+00:00
-- url     : https://prove2.me/theorems/ae3b6cd8-f789-4602-9a8d-e9c7480ec364
-- title:
--   (5.3) — tangent-loss estimate U_a(x) + U′_a(x)(z − x) − U_a(z) ≤ 4ξ_a(x)((z − x)/x)·log(z/x)
-- statement:
--   For $a>0$ and $0<x\le z$, with $U_a$ the scalar potential and $\xi_a(x)=U_a(x)-xU_a'(x)$,
--
--   $$U_a(x)+U_a'(x)(z-x)-U_a(z)\ \le\ 4\,\xi_a(x)\,\frac{z-x}{x}\,\log(z/x).$$
--
--   The left side is the error of the tangent line of the concave function $U_a$ at $x$, evaluated at $z$. It bounds the loss on the vertices whose weights are increased in Lemma 5.4.
--
--   Differences from the source: none.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 21 (PDF 22), §5.3, (5.3); proved p. 49 (PDF 50), Appendix A

import Mathlib
import Definitions.Def_FracColorLocal_KrFree_Potential

namespace FracColorLocal.KrFree

/-- (5.3): the tangent-loss estimate for `U_a` when the weight increases from `x` to `z`. -/
theorem eq_5_3 (a x z : ℝ) (ha : 0 < a) (hx : 0 < x) (hxz : x ≤ z) :
    scalarU a x + deriv (scalarU a) x * (z - x) - scalarU a z ≤
      4 * xiScalar a x * ((z - x) / x) * Real.log (z / x) := by sorry

end FracColorLocal.KrFree
