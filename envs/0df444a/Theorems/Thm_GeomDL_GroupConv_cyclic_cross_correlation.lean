-- Prove2me | Theorems.Thm_GeomDL_GroupConv_cyclic_cross_correlation
-- name    : GeomDL.GroupConv.cyclic_cross_correlation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:25.896782+00:00
-- url     : https://prove2.me/theorems/18bfed21-0b92-471f-aaa5-7458d67d6c9c
-- title:
--   §4.3, p. 42 — cyclic group convolution is cross-correlation
-- statement:
--   Let $n>0$ and let the cyclic shift group $G=\mathbb Z_n$ act on the index set $\Omega=\mathbb Z_n$ by $g\cdot v=v-u$, where the shift $g$ is identified with the index $u$. For scalar signals $x,\theta:\mathbb Z_n\to\mathbb R$, equation (14) with counting measure becomes
--
--   $$
--   (x\star\theta)(u)=\sum_{v=0}^{n-1}x_v\theta_{v+u\pmod n}.
--   $$
--
--   This is the cyclic cross-correlation formula that the book calls convolution and explicitly identifies as cross-correlation in its side-note.
--
--   **Formalization Note** The left-hand side is the general group convolution (14) of this mission, `groupConvolution`, taken with the counting measure on `ZMod n` (the side-note's "in case µ is discrete, this means summing over Ω") at the shift `CyclicShiftGroup.ofShift u` identified with $u$; the group is the separate type `CyclicShiftGroup n` acting by $v\mapsto v-u$. The inverse shift and the resulting sign $v+u$ are therefore part of the claim, not of a definition. $n>0$ makes the cyclic index set the printed $\{0,\ldots,n-1\}$.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.3, pp. 41–42, cyclic example and cross-correlation side-note p. 42

import Mathlib
import Definitions.Def_GeomDL_GroupConv_Model

namespace GeomDL.GroupConv

/-- §4.3, pp. 41–42: equation (14) on `Ω = ℤ_n` with the cyclic shift group `g.v = v - u`
and the counting measure ("in case µ is discrete, this means summing over Ω") is
cross-correlation. -/
theorem cyclic_cross_correlation (n : ℕ) [NeZero n] (x θ : ZMod n → ℝ) (u : ZMod n) :
    groupConvolution (MeasureTheory.Measure.count : MeasureTheory.Measure (ZMod n)) x θ
      (CyclicShiftGroup.ofShift u) = ∑ v : ZMod n, x v * θ (v + u) := by sorry

end GeomDL.GroupConv
