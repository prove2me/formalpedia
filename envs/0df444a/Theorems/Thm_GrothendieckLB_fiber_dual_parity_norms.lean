-- Prove2me | Theorems.Thm_GrothendieckLB_fiber_dual_parity_norms
-- name    : GrothendieckLB.fiber_dual_parity_norms
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T16:18:23.709203+00:00
-- url     : https://prove2.me/theorems/21f36ebb-cde5-49cf-a463-f8e497433555
-- title:
--   Gaussian cubic dual bound from the norms of its even and odd parts
-- statement:
--   Let $Z$ be a standard normal variable, let $\nu=\sqrt{2/\pi}$, and let $p=\sum_{j=0}^3 a_j\mathrm{He}_j$ be expressed in the normalized probabilists’ Hermite basis with $\sum_j a_j^2=1$. For every $7/5\le c\le 12$,$$\mathbb E\,(|p(Z)|-c|Z|)_+\le\frac{3\nu}{2}\big(\sqrt{1+c^2}-c\big).$$ This interval is the portion of the intermediate-price estimate controlled by the separate Euclidean norms of the even and odd Hermite coefficients.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, Appendix D.3, equation (56), https://arxiv.org/html/2608.11158v2#A4.SS3. The subdivision at 7/5 is used in this formal proof.

import Mathlib
import Definitions.Def_ABPOnline_cG
import Definitions.Def_GrothendieckLB_he
import Definitions.Def_GrothendieckLB_stdExp

namespace GrothendieckLB

theorem fiber_dual_parity_norms (a : Fin 4 → ℝ) (ha : ∑ j, a j ^ 2 = 1) (c : ℝ)
    (hlo : (7 : ℝ) / 5 ≤ c) (hhi : c ≤ 12) :
    stdExp (fun s => max (|∑ j, a j * he j s| - c * |s|) 0) ≤
      (3 * ABPOnline.cG / 2) * (Real.sqrt (1 + c ^ 2) - c) := by sorry

end GrothendieckLB
