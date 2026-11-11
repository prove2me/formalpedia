-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_eq_4_1_4_4
-- name    : FracColorLocal.KrFree.eq_4_1_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:13:22.534197+00:00
-- url     : https://prove2.me/theorems/db7749f5-0bd0-4fa6-835f-294b368c6494
-- title:
--   (4.1) and (4.4) — U_a is increasing and concave with 0 < U_a ≤ a; unique minimizer d∗, −af′(d∗) = x², U′_a = 2d∗x; bounds on ξ_a
-- statement:
--   Fix $a>0$ and let $U_a(x)=\inf_{t>0}\{af(t)+tx^2\}$ for $x>0$, $U_a(0)=0$, with $f$ Shearer's function. Then:
--
--   1. $U_a$ is increasing and concave on $[0,\infty)$, and $0<U_a(x)\le a$ for $x>0$.
--   2. For $x>0$ the infimum has a unique minimizer $d_*=d_*(a,x)>0$, characterized among $t>0$ by $-af'(d_*)=x^2$, and $U_a$ is differentiable at $x$ with
--   $$U_a'(x)=2d_*x. \tag{4.1}$$
--   3. With $\xi_a(x)=U_a(x)-xU_a'(x)$,
--   $$0<\xi_a(x)\le U_a(x)\le a,\qquad d_*\xi_a(x)\le a,\qquad (1+d_*)\xi_a(x)+2d_*x^2=a. \tag{4.4}$$
--
--   These scalar facts drive every potential computation of §4–§5 (Lemma 4.3, Corollary 5.5).
--
--   Differences from the source:
--   - reading: "U_a is increasing" → strictly increasing on $[0,\infty)$; reason: Appendix A proves $U'>0$ on $(0,\infty)$ and $U_a(0)=0<U_a(x)$, so the strict reading is the one proved (the stronger of the two readings).
--   - reading: "concave" → concave on $[0,\infty)$; reason: Appendix A: "continuity extends concavity to $[0,\infty)$", and $U_a$ is defined on $[0,\infty)$.
--   - encoding: "the unique minimizer $d_*(a,x)$" → the definition `dStar` (a chosen positive minimizer, `0` if none) together with the asserted existence, attainment and uniqueness; reason: Lean needs a total function; the item asserts that it is the unique minimizer.
--   - encoding: "characterized by $-af'(d_*)=x^2$" → for every $t>0$: $t$ attains the infimum iff $-af'(t)=x^2$; reason: this is what "characterized by" means.
--   - encoding: "$U_a'(x)=2d_*x$" → `HasDerivAt (scalarU a) (2 * dStar a x * x) x`; reason: asserts differentiability as well as the value.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 17 (PDF 18), §4.1, (4.1); p. 18 (PDF 19), §4.2, (4.4); proved pp. 48–49 (PDF 49–50), Appendix A

import Mathlib
import Definitions.Def_FracColorLocal_KrFree_Shearer
import Definitions.Def_FracColorLocal_KrFree_Potential

namespace FracColorLocal.KrFree

/-- (4.1) and (4.4): scalar facts on `U_a`, its minimizer `d∗(a, x)` and `ξ_a`. -/
theorem eq_4_1_4_4 (a : ℝ) (ha : 0 < a) :
    StrictMonoOn (scalarU a) (Set.Ici 0) ∧
    ConcaveOn ℝ (Set.Ici 0) (scalarU a) ∧
    ∀ x : ℝ, 0 < x →
      (0 < scalarU a x ∧ scalarU a x ≤ a) ∧
      -- `d∗(a, x)` is a positive minimizer of `t ↦ a f(t) + t x²` over `t > 0` ...
      (0 < dStar a x ∧
        a * shearerF (dStar a x) + dStar a x * x ^ 2 = scalarU a x) ∧
      -- ... the unique one ...
      (∀ d : ℝ, 0 < d → a * shearerF d + d * x ^ 2 = scalarU a x → d = dStar a x) ∧
      -- ... characterized by `-a f'(d∗) = x²` ...
      (∀ d : ℝ, 0 < d → (a * shearerF d + d * x ^ 2 = scalarU a x ↔ -a * deriv shearerF d = x ^ 2)) ∧
      -- ... and `U'_a(x) = 2 d∗ x` (4.1).
      HasDerivAt (scalarU a) (2 * dStar a x * x) x ∧
      -- (4.4)
      (0 < xiScalar a x ∧ xiScalar a x ≤ scalarU a x ∧ scalarU a x ≤ a ∧
        dStar a x * xiScalar a x ≤ a ∧
        (1 + dStar a x) * xiScalar a x + 2 * dStar a x * x ^ 2 = a) := by sorry

end FracColorLocal.KrFree
