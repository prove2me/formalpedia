-- Prove2me | Theorems.Thm_OAI_ThreeManifold_NonpositiveMetric_CNMidpoint_axisShift_mul
-- name    : OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.axisShift_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:00:04.572339+00:00
-- url     : https://prove2.me/theorems/dd74c1fa-5f4a-4322-95a6-1b6efce40d1a
-- title:
--   The shift along an axis is additive on isometries commuting with the axial translation
-- statement:
--   Let $(X,d)$ be a proper metric space with a CN midpoint map $m$, i.e. $d(m(x,y),z)^2\le\tfrac12\big(d(x,z)^2+d(y,z)^2\big)-\tfrac14 d(x,y)^2$ for all $x,y,z\in X$. Let $c:\mathbb{R}\to X$ be an isometric embedding (a geodesic line). For $y\in X$, let $\pi_c(y)\in\mathbb{R}$ be a parameter of a nearest point of the line to $y$, i.e. $d(y,c(\pi_c(y)))\le d(y,c(s))$ for all $s\in\mathbb{R}$; such a parameter exists by properness and is unique because of the CN inequality. For a bijective isometry $k$ of $X$, define its *shift along $c$* as
--   $$
--   \tau_c(k)=\pi_c\big(k(c(0))\big).
--   $$
--
--   **Theorem.** Let $f$ be a bijective isometry of $X$ that translates the line $c$ by some $L>0$, i.e. $f(c(t))=c(t+L)$ for all $t\in\mathbb{R}$. If $g$ and $h$ are bijective isometries of $X$ that each commute with $f$, then
--   $$
--   \tau_c(g\circ h)=\tau_c(g)+\tau_c(h).
--   $$
--
--   Thus $\tau_c$ is a homomorphism from the centralizer of $f$ in the isometry group to $(\mathbb{R},+)$. In particular it sends inverses to negatives and commutators to $0$. This is the additive invariant used to obstruct certain commutator relations among isometries of nonpositively curved spaces.
--
--   **Formalization Note** Isometries are elements of the group `X ≃ᵢ X`, whose product is composition, $(g*h)(x)=g(h(x))$. The coordinate $\pi_c$ is `lineCoordinate`, which picks a minimizer by choice, and $\tau_c$ is `axisShift c hc`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Convexity.lean#L512-L533

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

open OAI OAI.ThreeManifold OAI.ThreeManifold.NonpositiveMetric OAI.ThreeManifold.NonpositiveMetric.CNMidpoint
open Set Filter Topology Function
variable {X : Type*} [MetricSpace X] [ProperSpace X] (C : CNMidpoint X)
include C

theorem OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.axisShift_mul {f : X ≃ᵢ X} (c : ℝ → X) (hc : Isometry c)
    {L : ℝ} (hL : 0 < L) (hfc : ∀ t, f (c t) = c (t+L))
    (g h : X ≃ᵢ X) (hfg : Commute f g) (hfh : Commute f h) :
    axisShift c hc (g*h) = axisShift c hc g + axisShift c hc h := by sorry
