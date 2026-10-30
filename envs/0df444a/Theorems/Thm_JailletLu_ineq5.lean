-- Prove2me | Theorems.Thm_JailletLu_ineq5
-- name    : JailletLu.ineq5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:30:20.666653+00:00
-- url     : https://prove2.me/theorems/97209c93-6a22-44c4-ae4c-6367fea0a739
-- title:
--   Inequality (5): $h(y,0)-h(y,x)\le -x\,\partial_2h(y,0)\le e^{-1}x$
-- statement:
--   Let $h$ be the function of Claim 2. For every $y\in[0,1]$ and $x\in[0,y]$,
--   $$
--   h(y,0)-h(y,x)\ \le\ -x\cdot\frac{\partial h}{\partial x}(y,0)\ \le\ e^{-1}x,
--   $$
--   where $\frac{\partial h}{\partial x}(y,0)$ is the derivative of $h(y,\cdot)$ at $0$. In §5.4 it is applied with $y=f_{a_1}$ and $x=m_{a_1,a}$: the probability $P(E_{a_1,a})=g(f_{a_1},m_{a_1,a})$ is at most $e^{-1}m_{a_1,a}$.
--
--   Differences from the source:
--   - reading: ∂h/∂y (f_{a1}, 0) → the derivative of h(y, ·) in its second argument at 0; reason: the sentence before (5) invokes "the convexity of h in the second argument"; with the first argument the middle term is −x e^{−y} < 0 and (5) would be false
--   - reading: (5) opens with P(E_{a1,a}) = h(f_{a1}, 0) − h(f_{a1}, m_{a1,a}) → the two inequalities about h only; reason: that equality is Claim 2 (p. 14) recalled, whose probability model this mission does not build; the content of (5) used later ("from inequality (5)") is the two inequalities
--   - generalization: the pairs (f_{a1}, m_{a1,a}) → every (y, x) with 0 ≤ x ≤ y ≤ 1; reason: every pair of the paper satisfies 0 ≤ m_{a1,a} ≤ f_{a1} ≤ 1, so the statement specializes to it
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 15, (5)

import Mathlib
import Definitions.Def_JailletLu_h

namespace JailletLu

/-- **Inequality (5).**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 15, (5): "Because of the convexity of h in the second argument, we have
P(E_{a1,a}) = h(f_{a1}, 0) − h(f_{a1}, m_{a1,a}) ≤ −m_{a1,a} · ∂h/∂y (f_{a1}, 0) ≤ e^{−1} m_{a1,a}".

Conclusion: for `y ∈ [0, 1]` and `x ∈ [0, y]`,
`h(y, 0) − h(y, x) ≤ −x · ∂₂h(y, 0) ≤ e^{−1} x`, where `∂₂h(y, 0)` is the derivative of `h(y, ·)` at `0`.

**Formalization Note.** The derivative is in the *second* argument (the sentence before (5) says
"convexity of h in the second argument"; with the first argument the bound would be negative and
false). The equality `P(E_{a1,a}) = h(f_{a1},0) − h(f_{a1},m_{a1,a})` recalls Claim 2 (p. 14), whose
probability model this mission does not build. The pair `(f_{a1}, m_{a1,a})` is replaced by any
`(y, x)` with `0 ≤ x ≤ y ≤ 1`, which covers every pair of the paper. -/
theorem ineq5 (y x : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hx0 : 0 ≤ x) (hxy : x ≤ y) :
    h y 0 - h y x ≤ -x * deriv (h y) 0 ∧ -x * deriv (h y) 0 ≤ Real.exp (-1) * x := by sorry

end JailletLu
