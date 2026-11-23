-- Prove2me | Theorems.Thm_GrothendieckLB_fiber_dual_tail
-- name    : GrothendieckLB.fiber_dual_tail
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T15:24:33.449809+00:00
-- url     : https://prove2.me/theorems/dcdfaf03-08dc-45ef-bd6c-1f8a2c668a2b
-- title:
--   The one-dimensional cubic Gaussian dual inequality at large prices
-- statement:
--   Let $Z$ be standard normal, $\nu=\sqrt{2/\pi}$, and $p=\sum_{j=0}^3 a_j\mathrm{He}_j$ be a real cubic in the normalized probabilists’ Hermites with $\sum a_j^2=1$. For every price $c\ge 12$, $$\mathbb E\big[(|p(Z)|-c|Z|)_+\big]\le \frac{3\nu}{2}\big(\sqrt{1+c^2}-c\big).$$ The paper rescales by $1/c$, localizes the positive part near zero, estimates the remote tail, and bounds the remaining integral in local and complementary parameter regions.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, Appendix D, equation (56) and Section D.4, certificate (C3), https://arxiv.org/html/2608.11158v2#A4

import Mathlib
import Definitions.Def_ABPOnline_cG
import Definitions.Def_GrothendieckLB_he
import Definitions.Def_GrothendieckLB_stdExp

namespace GrothendieckLB

theorem fiber_dual_tail (a : Fin 4 → ℝ) (ha : ∑ j, a j ^ 2 = 1) (c : ℝ)
    (hlo : (12 : ℝ) ≤ c) :
    stdExp (fun s => max (|∑ j, a j * he j s| - c * |s|) 0) ≤
      (3 * ABPOnline.cG / 2) * (Real.sqrt (1 + c ^ 2) - c) := by sorry

end GrothendieckLB
