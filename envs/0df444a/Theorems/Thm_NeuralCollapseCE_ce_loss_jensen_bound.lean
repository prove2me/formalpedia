-- Prove2me | Theorems.Thm_NeuralCollapseCE_ce_loss_jensen_bound
-- name    : NeuralCollapseCE.ce_loss_jensen_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:10:52.360798+00:00
-- url     : https://prove2.me/theorems/29cc8f9e-d405-487e-a23e-5803749131d3
-- title:
--   Theorem 1, eq. (11): Jensen lower bound for the cross-entropy loss
-- statement:
--   Let $n\ge2$ and let $u_1,\dots,u_n,v_1,\dots,v_n\in\mathbb{R}^d$ be unit vectors, with $U=\sum_iu_i$ and $V=\sum_iv_i$. Then
--
--   $$\mathcal{L}(u,v)\ \ge\ n\log\Big[1+(n-1)\exp\Big(\frac1n\Big(\frac{\langle V,U\rangle}{n-1}-\frac{n}{n-1}\sum_{i=1}^n\langle v_i,u_i\rangle\Big)\Big)\Big].$$
--
--   This is inequality (11) in the proof of Theorem 1, obtained from Jensen's inequality for the exponential (9) and for the convex function $t\mapsto\log(1+ae^{t})$. It reduces Theorem 1 to bounding the quadratic form $n\sum_i\langle v_i,u_i\rangle-\langle V,U\rangle$.
-- source:
--   Lu and Steinerberger, Neural collapse with cross-entropy loss, arXiv:2012.08465v2 (2021), Section 3 (proof of Theorem 1), eqs. (9)-(11), p. 7

import Mathlib
import Definitions.Def_NeuralCollapseCE_Basic

open MeasureTheory Filter Topology Asymptotics

namespace NeuralCollapseCE

theorem ce_loss_jensen_bound {n d : ℕ} (hn : 2 ≤ n) (u v : Fin n → Vec d)
    (hu : IsUnitConfig u) (hv : IsUnitConfig v) :
    (n : ℝ) * Real.log (1 + ((n : ℝ) - 1) * Real.exp ((1 / (n : ℝ)) *
        (inner ℝ (∑ i, v i) (∑ i, u i) / ((n : ℝ) - 1) -
          (n : ℝ) / ((n : ℝ) - 1) * ∑ i, inner ℝ (v i) (u i)))) ≤
      ceLoss u v := by sorry

end NeuralCollapseCE
