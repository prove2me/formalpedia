-- Prove2me | Theorems.Thm_GrothendieckLB_fiber_dual_medium
-- name    : GrothendieckLB.fiber_dual_medium
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T15:24:39.501383+00:00
-- url     : https://prove2.me/theorems/ad8603d8-804f-4889-a4af-d7937e592cdb
-- title:
--   The one-dimensional cubic Gaussian dual inequality at intermediate prices
-- statement:
--   Let $Z$ be standard normal, $\nu=\sqrt{2/\pi}$, and $p=\sum_{j=0}^3 a_j\mathrm{He}_j$ be a real cubic in the normalized probabilists’ Hermites with $\sum a_j^2=1$. For every price $993405/1000000\le c\le 12$, $$\mathbb E\big[(|p(Z)|-c|Z|)_+\big]\le \frac{3\nu}{2}\big(\sqrt{1+c^2}-c\big).$$ The paper verifies this range by splitting the even and odd Hermite components, bounding the Gaussian integral on panels, and covering the even coefficient disk.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, Appendix D, equation (56) and Section D.3, certificate (C2), https://arxiv.org/html/2608.11158v2#A4

import Mathlib
import Definitions.Def_ABPOnline_cG
import Definitions.Def_GrothendieckLB_he
import Definitions.Def_GrothendieckLB_stdExp

namespace GrothendieckLB

theorem fiber_dual_medium (a : Fin 4 → ℝ) (ha : ∑ j, a j ^ 2 = 1) (c : ℝ)
    (hlo : (993405 : ℝ) / 1000000 ≤ c) (hhi : c ≤ 12) :
    stdExp (fun s => max (|∑ j, a j * he j s| - c * |s|) 0) ≤
      (3 * ABPOnline.cG / 2) * (Real.sqrt (1 + c ^ 2) - c) := by sorry

end GrothendieckLB
