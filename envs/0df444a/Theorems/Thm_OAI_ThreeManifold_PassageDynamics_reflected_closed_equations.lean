-- Prove2me | Theorems.Thm_OAI_ThreeManifold_PassageDynamics_reflected_closed_equations
-- name    : OAI.ThreeManifold.PassageDynamics.reflected_closed_equations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:31:58.105723+00:00
-- url     : https://prove2.me/theorems/85ce9e9e-7a69-4ac5-baf4-bf0036d5c081
-- title:
--   Even/odd reflection about a turning point again solves $t'=v,\ v'=-\tfrac12F(t)$
-- statement:
--   For $c\in\mathbb{R}$ and $f:\mathbb{R}\to\mathbb{R}$ define the even and odd reflections of $f$ about $c$ by
--   $$
--   (R^+_c f)(s)=\begin{cases} f(s) & s\le c,\\ f(2c-s) & s>c,\end{cases}\qquad (R^-_c f)(s)=\begin{cases} f(s) & s\le c,\\ -f(2c-s) & s>c.\end{cases}
--   $$
--
--   Let $F:\mathbb{R}\to\mathbb{R}$ be $C^\infty$, let $a<c<b$, and let $t,v:\mathbb{R}\to\mathbb{R}$ satisfy, at every $s\in[a,b]$ (with two-sided derivatives),
--   $$
--   t'(s)=v(s),\qquad v'(s)=-\tfrac12F(t(s)),
--   $$
--   and assume $v(c)=0$. Then for every $s\in[a,\,2c-a]$ the reflected pair $(R^+_ct,\,R^-_cv)$ is differentiable at $s$ and
--   $$
--   (R^+_c t)'(s)=(R^-_c v)(s),\qquad (R^-_c v)'(s)=-\tfrac12F\big((R^+_c t)(s)\big).
--   $$
--
--   No relation between $b$ and $2c-a$ is assumed: only the part of the solution on $[a,c]$ is used to the right of $c$. The result says that reflecting a solution about a turning point produces a solution of the same autonomous equation on the doubled interval $[a,2c-a]$, the basic tool for completing a half passage into a symmetric one.
--
--   **Formalization Note** $R^+_c$ and $R^-_c$ are `reflectEven c` and `reflectOdd c`; derivatives are `HasDerivAt`, so at the endpoints $a$ and $2c-a$ they are two-sided derivatives of the functions defined on all of $\mathbb{R}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Passages.lean#L843-L867

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

theorem OAI.ThreeManifold.PassageDynamics.reflected_closed_equations {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {t v : ℝ → ℝ}
    {a b c : ℝ} (hc : c ∈ Ioo a b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F (t s)/2) s) (hvc : v c = 0) :
    ∀ s ∈ Icc a (2*c-a),
      HasDerivAt (reflectEven c t) (reflectOdd c v s) s ∧
      HasDerivAt (reflectOdd c v) (-F (reflectEven c t s)/2) s := by sorry
