-- Prove2me | Theorems.Thm_OAI_TriangularCovering_sector_weights
-- name    : OAI.TriangularCovering.sector_weights
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:50:15.056768+00:00
-- url     : https://prove2.me/theorems/7b03e304-76ae-45a1-9744-e02d5f7d5c0e
-- title:
--   Barycentric weights for a point of the triangle with vertices $(0,0)$, $(aT,T)$, $(bT,T)$
-- statement:
--   Let $a<b$ and $T>0$ be real numbers, and let $y,t\in\mathbb{R}$ satisfy $0\le t\le T$ and $at\le y\le bt$. Then there exist real numbers $r,s$ with
--   $$
--   r\ge0,\qquad s\ge0,\qquad r+s\le1,\qquad rT+sT=t,\qquad r\,(aT)+s\,(bT)=y .
--   $$
--
--   Geometrically, the hypotheses say that the point $(y,t)$ lies in the planar triangle with vertices $(0,0)$, $(aT,T)$, $(bT,T)$, that is, between the rays $y=at$ and $y=bt$ and at height at most $T$. The conclusion gives barycentric weights $(y,t)=(1-r-s)(0,0)+r(aT,T)+s(bT,T)$. The lemma is used to show that a point satisfying a sector-and-cutoff condition lies in the base triangle of a lower or an upper cylinder of the covering of the tetrahedron.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/CylinderFamily.lean#L106-L122

import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
import Definitions.Def_OAI_Geometry_TriangularCovering_Projection
import Definitions.Def_OAI_Geometry_TriangularCovering_CylinderFamily

open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem OAI.TriangularCovering.sector_weights {a b T y t : ℝ} (hab : a < b) (hT : 0 < T)
    (_ht0 : 0 ≤ t) (htT : t ≤ T) (hay : a*t ≤ y) (hyb : y ≤ b*t) :
    ∃ r s : ℝ, 0 ≤ r ∧ 0 ≤ s ∧ r+s ≤ 1 ∧ r*T+s*T=t ∧ r*(a*T)+s*(b*T)=y := by sorry
