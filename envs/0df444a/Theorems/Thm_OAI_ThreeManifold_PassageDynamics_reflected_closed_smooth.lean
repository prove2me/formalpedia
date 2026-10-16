-- Prove2me | Theorems.Thm_OAI_ThreeManifold_PassageDynamics_reflected_closed_smooth
-- name    : OAI.ThreeManifold.PassageDynamics.reflected_closed_smooth
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:47:01.943199+00:00
-- url     : https://prove2.me/theorems/16373f32-7837-4890-86e8-fcbaaac31b01
-- title:
--   Even/odd reflection of a smooth solution of $t''=-\tfrac12F(t)$ about a turning point is smooth
-- statement:
--   For $c\in\mathbb{R}$ and $f:\mathbb{R}\to\mathbb{R}$ define the even and odd reflections of $f$ about $c$ by
--   $$
--   (R^+_c f)(s)=\begin{cases} f(s) & s\le c,\\ f(2c-s) & s>c,\end{cases}\qquad (R^-_c f)(s)=\begin{cases} f(s) & s\le c,\\ -f(2c-s) & s>c.\end{cases}
--   $$
--
--   Let $F:\mathbb{R}\to\mathbb{R}$ be $C^\infty$, let $a<c<b$, and let $t,v:\mathbb{R}\to\mathbb{R}$ satisfy at every $s\in[a,b]$
--   $$
--   t'(s)=v(s),\qquad v'(s)=-\tfrac12F(t(s)),
--   $$
--   with $v(c)=0$. Assume moreover that $t$ and $v$ are $C^\infty$ at every point of $[a,b]$ (that is, $C^\infty$ on some neighbourhood of each such point). Then $R^+_ct$ and $R^-_cv$ are $C^\infty$ at every point $s\in[a,\,2c-a]$.
--
--   The only delicate point is the turning point $c$, where the piecewise definition switches branches; the local time symmetry of solutions about a turning point makes the two branches glue smoothly. Together with the fact that the reflected pair solves the same equation, this lets a half passage be completed into a smooth symmetric passage on $[a,2c-a]$.
--
--   **Formalization Note** $R^+_c$ and $R^-_c$ are `reflectEven c` and `reflectOdd c`; smoothness at a point is `ContDiffAt ℝ ∞`. No relation between $b$ and $2c-a$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Passages.lean#L869-L890

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity
import Definitions.Def_OAI_Geometry_ConjugatePoints_FundamentalGroup
import Definitions.Def_OAI_Geometry_ConjugatePoints_Passages

open OAI OAI.ThreeManifold OAI.ThreeManifold.PassageDynamics
open Set Filter Topology
open scoped ContDiff

theorem OAI.ThreeManifold.PassageDynamics.reflected_closed_smooth {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {t v : ℝ → ℝ}
    {a b c : ℝ} (hc : c ∈ Ioo a b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F (t s)/2) s) (hvc : v c = 0)
    (hta : ∀ s ∈ Icc a b, ContDiffAt ℝ ∞ t s)
    (hva : ∀ s ∈ Icc a b, ContDiffAt ℝ ∞ v s) :
    ∀ s ∈ Icc a (2*c-a), ContDiffAt ℝ ∞ (reflectEven c t) s ∧ ContDiffAt ℝ ∞ (reflectOdd c v) s := by sorry
