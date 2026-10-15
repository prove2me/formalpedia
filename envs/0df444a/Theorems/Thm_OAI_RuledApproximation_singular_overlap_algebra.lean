-- Prove2me | Theorems.Thm_OAI_RuledApproximation_singular_overlap_algebra
-- name    : OAI.RuledApproximation.singular_overlap_algebra
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:15:55.767445+00:00
-- url     : https://prove2.me/theorems/51b0162d-a854-47b5-a227-61005997bd98
-- title:
--   Algebraic overlap inequality: one of two perturbed heights stays below its ceiling
-- statement:
--   Let $\Delta_p(b)=b^2\big(\tfrac p4+(2-p)b^2\big)$. Consider real numbers $p,K,c,x,y$ and two copies $b_{\pm},r_{\pm},P_{\pm},Q_{\pm}$ (indexed by $-$ and $+$) satisfying the following hypotheses.
--
--   1. Parameters: $p\le2$, $K\ge1$, $0\le c\le1$, $cK\le\tfrac12$ and $16K^2c^3\le2c^{5/2}$.
--   2. Ranges: $|x|\le1$, $|y|\le1$, $r_{-}\ge\tfrac12$ and $r_{+}\ge\tfrac12$.
--   3. Estimates: $|P_{-}|\le K$ and $|P_{+}|\le K$; $|Q_{-}-b_{-}|\le K(r_{-}-\tfrac12)$ and $|Q_{+}-b_{+}|\le K(r_{+}-\tfrac12)$; $\big|P_{-}-(\tfrac p4+(2-p)y^2)\big|\le K\big(|b_{-}-y|+(r_{-}-\tfrac12)\big)$ and $\big|P_{+}-(\tfrac p4+(2-p)x^2)\big|\le K\big(|b_{+}-x|+(r_{+}-\tfrac12)\big)$; $|\Delta_p(b_{-})-\Delta_p(y)|\le K|b_{-}-y|$ and $|\Delta_p(b_{+})-\Delta_p(x)|\le K|b_{+}-x|$.
--   4. Equations:
--
--   $$
--   b_{-}=y-c\,x\,P_{-},\qquad b_{+}=x+c\,y\,P_{+},\qquad r_{-}+r_{+}=1+c\,\big(y\,Q_{+}-x\,Q_{-}\big).
--   $$
--
--   **Theorem.** Under these hypotheses,
--
--   $$
--   r_{-}\le\tfrac12+c^2\Delta_p(b_{-})+c^{5/2}\qquad\text{or}\qquad r_{+}\le\tfrac12+c^2\Delta_p(b_{+})+c^{5/2}.
--   $$
--
--   This is the purely algebraic core of the overlap step in the singular covering of the regular tetrahedron. There, $(b_{\pm},r_{\pm})$ are the two base points from which the lower and the upper family of ruled segments reach a given point, $P_{\pm}$ and $Q_{\pm}$ are the two components of the singular field at these base points, and the estimates in item 3 are those available near the level $r=\tfrac12$. The conclusion says that at least one of the two base points lies under the ceiling $\tfrac12+c^2\Delta_p+c^{5/2}$ of the base domain.
--
--   **Formalization Note** In Lean the indices $-$ and $+$ are the name suffixes `m` and `p` (as in `bm`, `rp`, `Qm`), $\Delta_p$ is `ceilingPolynomial p`, and $c^{5/2}$ is the real power `c^(5/2:ℝ)`, which is the usual one since $c\ge0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SingularOverlap.lean#L102-L200

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.singular_overlap_algebra {p K c x y bm bp rm rp Pm Pp Qm Qp : ℝ}
    (hp2 : p ≤ 2) (hK : 1 ≤ K) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcK : c*K ≤ 1/2) (hcsmall : 16*K^2*c^3 ≤ 2*c^(5/2:ℝ))
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hrm : 1/2 ≤ rm) (hrp : 1/2 ≤ rp)
    (hPm : |Pm| ≤ K) (hPp : |Pp| ≤ K)
    (hQm : |Qm-bm| ≤ K*(rm-1/2)) (hQp : |Qp-bp| ≤ K*(rp-1/2))
    (hPmy : |Pm-(p/4+(2-p)*y^2)| ≤ K*(|bm-y|+(rm-1/2)))
    (hPpx : |Pp-(p/4+(2-p)*x^2)| ≤ K*(|bp-x|+(rp-1/2)))
    (hdm : |ceilingPolynomial p bm-ceilingPolynomial p y| ≤ K*|bm-y|)
    (hdp : |ceilingPolynomial p bp-ceilingPolynomial p x| ≤ K*|bp-x|)
    (hbm : bm=y-c*x*Pm) (hbp : bp=x+c*y*Pp)
    (hsum : rm+rp=1+c*(y*Qp-x*Qm)) :
    rm ≤ 1/2+c^2*ceilingPolynomial p bm+c^(5/2:ℝ) ∨
    rp ≤ 1/2+c^2*ceilingPolynomial p bp+c^(5/2:ℝ) := by sorry
