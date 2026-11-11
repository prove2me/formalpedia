-- Prove2me | Theorems.Thm_OrderSelProphet_Kernel_lemma_F_1
-- name    : OrderSelProphet.Kernel.lemma_F_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:58:53.602465+00:00
-- url     : https://prove2.me/theorems/7cee9217-630a-4fce-add0-8334e147e3f6
-- title:
--   Lemma F.1 — kernel validity: $p_1\ge0$ with marginals $e^{-a}$ and $re^{-r}$, so $K_1$ is an allocation kernel; the perturbation vanishes for $r\ge10$
-- statement:
--   The density $p_1$ of (67) is nonnegative and has marginals
--   $$\int_0^\infty p_1(a,r)\,dr=e^{-a},\qquad\int_0^\infty p_1(a,r)\,da=re^{-r}.\quad(88)$$
--   Hence $K_1$ is an allocation kernel. For every fixed $a$, both $p_1(a,r)-p_0(a,r)$ and $\int_0^r(p_1(a,v)-p_0(a,v))\,dv$ vanish for $r\ge10$.
--
--   Differences from the source:
--   - encoding: p_1 nonnegative; marginals over a, r ∈ [0,∞); 'for every fixed a' → 0 ≤ p1 a r for all a, r ≥ 0; marginal identities for a ≥ 0, resp. r ≥ 0, with ∫ over (0,∞); vanishing for a ≥ 0 and r ≥ 10; reason: the exponential coordinates a, r range over [0,∞)
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Lemma F.1, p. 48

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_K1

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-- Lemma F.1 (Kernel validity), p. 48. -/
theorem lemma_F_1 :
    (∀ a r : ℝ, 0 ≤ a → 0 ≤ r → 0 ≤ p1 a r) ∧
      (∀ a : ℝ, 0 ≤ a → ∫ r in Ioi (0 : ℝ), p1 a r = Real.exp (-a)) ∧
      (∀ r : ℝ, 0 ≤ r → ∫ a in Ioi (0 : ℝ), p1 a r = r * Real.exp (-r)) ∧
      IsAllocationKernel K1 ∧
      ∀ a r : ℝ, 0 ≤ a → 10 ≤ r →
        p1 a r - p0 a r = 0 ∧ ∫ v in (0 : ℝ)..r, (p1 a v - p0 a v) = 0 := by sorry

end OrderSelProphet.Kernel
