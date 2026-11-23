-- Prove2me | Theorems.Thm_GrothendieckLB_dual_quadrature_sound
-- name    : GrothendieckLB.dual_quadrature_sound
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T16:31:46.279591+00:00
-- url     : https://prove2.me/theorems/af726e13-8243-463d-bef9-31eeecbf5bf6
-- title:
--   A verified quadrature certificate implies the Gaussian dual bound
-- statement:
--   For a normalized Hermite cubic, suppose a mesh covers the interval $[0,8]$ and its rational node and edge checks succeed. Suppose also that a finite tree covers the coefficient directions and both endpoints of a price interval pass the upper-sum tests. Then the Gaussian expected positive part at every price $c$ in that interval is at most $(3c_G/2)(\sqrt{1+c^2}-c)$.
-- source:
--   R. Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158v2, Appendix D.3, Lemma D.4 and Eq. (57), pp. 50–52. The interpolation-based quadrature and rational certificate adapt the construction by Igor Valuev in Prove2Me submission c940ceea-7150-49f4-b2ff-e3ae1aac955b.

import Mathlib
import Definitions.Def_ABPOnline_cG
import Definitions.Def_GrothendieckLB_he
import Definitions.Def_GrothendieckLB_stdExp
import Definitions.Def_GrothendieckLB_DualQuadrature

namespace GrothendieckLB

theorem dual_quadrature_sound (a : Fin 4 → ℝ) (ha : ∑ j, a j ^ 2 = 1) (c : ℝ)
    (nodes : List GrothendieckLB.DualQuadrature.Node)
    (v : GrothendieckLB.DualQuadrature.Band) (t : GrothendieckLB.DualQuadrature.Tree)
    (hz : GrothendieckLB.DualQuadrature.start nodes = true)
    (hn : GrothendieckLB.DualQuadrature.chainCheck nodes = true)
    (hv : GrothendieckLB.DualQuadrature.bandCheck v = true)
    (ht : GrothendieckLB.DualQuadrature.treeCheck nodes v GrothendieckLB.DualQuadrature.entire t = true)
    (hl : (v.lo : ℝ)/1000000 ≤ c) (hh : c ≤ (v.hi : ℝ)/1000000) :
    GrothendieckLB.stdExp (fun s => max (|∑ j, a j * GrothendieckLB.he j s| - c * |s|) 0) ≤
      (3 * ABPOnline.cG / 2) * (Real.sqrt (1 + c^2) - c) := by sorry

end GrothendieckLB
