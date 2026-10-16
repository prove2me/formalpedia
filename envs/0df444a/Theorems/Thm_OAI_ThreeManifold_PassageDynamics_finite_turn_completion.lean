-- Prove2me | Theorems.Thm_OAI_ThreeManifold_PassageDynamics_finite_turn_completion
-- name    : OAI.ThreeManifold.PassageDynamics.finite_turn_completion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:49:09.276986+00:00
-- url     : https://prove2.me/theorems/18a28ab2-f521-4ef8-9e29-9a51dc116574
-- title:
--   A passage of $t''=-\tfrac12F(t)$ from the wall with a turning point returns to the wall at time $2c-a$
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
--   with a turning point at $c$, $v(c)=0$. Assume the solution starts on the wall, $t(a)=0$, and stays strictly inside the slab, $t(s)\in(0,1)$ for all $s\in(a,b)$. Then:
--
--   1. $b\le 2c-a$;
--   2. $R^+_ct=t$ and $R^-_cv=v$ on $[a,b]$;
--   3. $(R^+_ct)(a)=0$ and $(R^+_ct)(2c-a)=0$;
--   4. $(R^+_ct)(s)\in(0,1)$ for every $s\in(a,\,2c-a)$.
--
--   So the given trajectory is an initial piece of the time-symmetric passage $R^+_ct$ on $[a,2c-a]$, which leaves the wall at time $a$, stays inside the slab $0<t<1$, and returns to the wall exactly at time $2c-a$; in particular the original trajectory cannot be continued inside the slab beyond $2c-a$. This is used to replace a possibly truncated neck passage by its complete symmetric return.
--
--   **Formalization Note** $R^+_c$ and $R^-_c$ are `reflectEven c` and `reflectOdd c`; derivatives are two-sided (`HasDerivAt`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Passages.lean#L892-L927

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

theorem OAI.ThreeManifold.PassageDynamics.finite_turn_completion {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {t v : ℝ → ℝ}
    {a b c : ℝ} (hc : c ∈ Ioo a b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F (t s)/2) s) (hvc : v c = 0)
    (ha : t a = 0) (hr : ∀ s ∈ Ioo a b, t s ∈ Ioo (0:ℝ) 1) :
    b ≤ 2*c-a ∧ EqOn (reflectEven c t) t (Icc a b) ∧ EqOn (reflectOdd c v) v (Icc a b) ∧
    reflectEven c t a = 0 ∧ reflectEven c t (2*c-a) = 0 ∧
    (∀ s ∈ Ioo a (2*c-a), reflectEven c t s ∈ Ioo (0:ℝ) 1) := by sorry
