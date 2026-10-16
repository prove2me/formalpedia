-- Prove2me | Theorems.Thm_OAI_ThreeManifold_PassageDynamics_scalar_enter_transverse
-- name    : OAI.ThreeManifold.PassageDynamics.scalar_enter_transverse
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:02:39.617153+00:00
-- url     : https://prove2.me/theorems/2eaa5cca-6be2-4329-9dc6-d984e3a0e15d
-- title:
--   A trajectory entering a half-line against a nonnegative force enters with positive speed
-- statement:
--   Consider the one-dimensional Newtonian system $\dot t=v$, $\dot v=-\tfrac12F(t)$, in which a nonnegative force $F$ pushes the position $t$ downwards.
--
--   **Statement.** Let $t,v,F:\mathbb R\to\mathbb R$, let $a<b$ and $r>0$. Assume that for every $s\in[a,b]$ the function $t$ is differentiable at $s$ with $\dot t(s)=v(s)$ and $v$ is differentiable at $s$ with $\dot v(s)=-\tfrac12F(t(s))$. Assume further that $t(a)=0$, that $t(s)>0$ for all $s\in(a,b)$, and that $F(x)\ge0$ for all $x<r$. Then
--   $$v(a)>0 .$$
--
--   In words: a trajectory that starts on the level $t=0$ and immediately moves into $\{t>0\}$, while the force near that level is nonnegative, must cross the level transversally. It is used to show that geodesics entering the neck through its lower boundary have strictly positive vertical speed there (and, after the substitutions $t\mapsto1-t$ or $s\mapsto a+b-s$, the analogous statements at the upper boundary and at exit times).
--
--   **Formalization Note** The derivative hypotheses are `HasDerivAt` at every point of the closed interval $[a,b]$, i.e. two-sided derivatives of functions defined on all of $\mathbb R$, also at the endpoints.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean#L974-L996

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
import Definitions.Def_OAI_Geometry_ConjugatePoints_NoConjugatePoints

open OAI OAI.ThreeManifold OAI.ThreeManifold.PassageDynamics
open Set Filter Topology
open Cometric Neck ReturningPassage

theorem OAI.ThreeManifold.PassageDynamics.scalar_enter_transverse {t v F : ℝ → ℝ} {a b r : ℝ} (hab : a < b)
    (hr : 0 < r) (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F (t s)/2) s)
    (ha : t a = 0) (hpos : ∀ s ∈ Ioo a b, 0 < t s)
    (hF : ∀ x < r, 0 ≤ F x) : 0 < v a := by sorry
