-- Prove2me | Theorems.Thm_HessianDamping_IPAHDSC_term2_nonneg
-- name    : HessianDamping.IPAHDSC.term2_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:59.066823+00:00
-- url     : https://prove2.me/theorems/fa24d2b9-a5a5-414c-a5cf-2686cc5437a6
-- title:
--   Term 2, proof of Theorem 9, p. 26 — (√µ/(2s) + µ/√s)X² + (β/4)Y² − √µXY ≥ 0 when √s ≤ β
-- statement:
--   Let $\mu>0$, $s>0$ and $\beta>0$, and put $a=\frac{\sqrt\mu}{2s}+\frac{\mu}{\sqrt s}$. Then:
--
--   1. if $a\ge\frac\mu\beta$, then for all real numbers $X,Y$,
--   $$aX^2+\frac\beta4Y^2-\sqrt\mu\,XY\ge0;$$
--   2. $a\ge\frac\mu\beta$ if and only if $\sqrt s\le\frac\beta2\big(1+\sqrt{1+\frac{2}{\beta\sqrt\mu}}\big)$;
--   3. if $\sqrt s\le\beta$, then $a\ge\frac\mu\beta$.
--
--   In the proof of Theorem 9 this is applied with $X=\|x_{k+1}-x_k\|$ and $Y=\|\nabla f(x_{k+1})\|$ to show that the second group of remainder terms is nonnegative under the step-size condition $\sqrt s\le\beta$.
--
--   **Formalization Note** $\beta>0$ is assumed so that $\mu/\beta$ is the page's quantity; under the theorem's hypotheses it follows from $0<\sqrt s\le\beta$.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 26, proof of Theorem 9, Term 2

import Mathlib
import Definitions.Def_HessianDamping_IPAHDSC_Setting

namespace HessianDamping.IPAHDSC

/-- Term 2, proof of Theorem 9, p. 26: if `√μ/(2s) + μ/√s ≥ μ/β` then
`(√μ/(2s) + μ/√s) X² + (β/4) Y² - √μ X Y ≥ 0` for all reals `X`, `Y`; the condition is
equivalent to `√s ≤ (β/2)(1 + √(1 + 2/(β√μ)))`; and `√s ≤ β` implies that condition. -/
theorem term2_nonneg (μ β s : ℝ) (hμ : 0 < μ) (hs : 0 < s) (hβ : 0 < β) :
    (Real.sqrt μ / (2 * s) + μ / Real.sqrt s ≥ μ / β →
      ∀ X Y : ℝ,
        0 ≤ (Real.sqrt μ / (2 * s) + μ / Real.sqrt s) * X ^ 2 + β / 4 * Y ^ 2 -
          Real.sqrt μ * X * Y) ∧
    (Real.sqrt μ / (2 * s) + μ / Real.sqrt s ≥ μ / β ↔
      Real.sqrt s ≤ β / 2 * (1 + Real.sqrt (1 + 2 / (β * Real.sqrt μ)))) ∧
    (Real.sqrt s ≤ β → Real.sqrt μ / (2 * s) + μ / Real.sqrt s ≥ μ / β) := by sorry

end HessianDamping.IPAHDSC
