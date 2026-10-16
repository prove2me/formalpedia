-- Prove2me | Theorems.Thm_OAI_ThreeManifold_NonpositiveMetric_CNMidpoint_cyclic_shear_obstruction
-- name    : OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.cyclic_shear_obstruction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:11:26.315982+00:00
-- url     : https://prove2.me/theorems/76b1f177-61b7-47c3-a0c0-5f3d37d75cc2
-- title:
--   Shear obstruction: two commuting semisimple isometries with $h=[a,b]$ and $hf=[c,d]$ cannot both act without fixed points
-- statement:
--   Let $(X,d)$ be a proper metric space with a CN midpoint map $m$, i.e. $d(m(x,y),z)^2\le\tfrac12\big(d(x,z)^2+d(y,z)^2\big)-\tfrac14 d(x,y)^2$ for all $x,y,z\in X$. Assume moreover that any two points lie on a complete constant-speed geodesic line: for all $x,y\in X$ there is $q:\mathbb{R}\to X$ with $q(0)=x$, $q(1)=y$ and
--   $$
--   d(q(s),q(t))=|s-t|\,d(x,y)\qquad\text{for all } s,t\in\mathbb{R}.
--   $$
--   For a map $k:X\to X$ let $\operatorname{Min}(k)=\{x\in X : d(x,k(x))\le d(y,k(y))\text{ for all }y\in X\}$ be the set where its displacement attains its infimum. Write $[a,b]=aba^{-1}b^{-1}$, with products of isometries taken as composition.
--
--   **Theorem.** There do not exist bijective isometries $f,h,a,b,c,d$ of $X$ satisfying all of the following:
--   1. $\operatorname{Min}(f)\neq\emptyset$ and $\operatorname{Min}(h)\neq\emptyset$;
--   2. $f$ and $h$ have no fixed points, i.e. $f(x)\neq x$ and $h(x)\neq x$ for all $x\in X$;
--   3. $f$ commutes with $h$, $a$ and $b$, and $h$ commutes with $c$ and $d$;
--   4. the relations
--   $$
--   h=[a,b]=aba^{-1}b^{-1},\qquad hf=[c,d]=cdc^{-1}d^{-1}
--   $$
--   hold.
--
--   Conditions 1–2 say that $f$ and $h$ are hyperbolic (semisimple with positive translation length). The theorem rules out a group configuration in which $h$, commuting with $f$, is a commutator of elements centralizing $f$ while its "sheared" product with another commuting element is again a commutator. In the intended application $X$ is the universal cover of a closed manifold with a nonpositively curved metric and the six isometries are deck transformations. The theorem then shows that a fundamental group containing such relations cannot act in this way.
--
--   **Formalization Note** Isometries are elements of the group `X ≃ᵢ X`, with product given by composition, and $\operatorname{Min}(k)$ is `minset k`. The conclusion is `False`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Convexity.lean#L696-L729

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

theorem OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.cyclic_shear_obstruction
    (hs : ∀ x y : X, ∃ q : ℝ → X, q 0 = x ∧ q 1 = y ∧
      ∀ s t, dist (q s) (q t) = |s-t| * dist x y)
    (f h a b c d : X ≃ᵢ X)
    (hfmin : (minset f).Nonempty) (hhmin : (minset h).Nonempty)
    (hfpos : ∀ x, f x ≠ x) (hhpos : ∀ x, h x ≠ x)
    (hfh : Commute f h) (hfa : Commute f a) (hfb : Commute f b)
    (hhc : Commute h c) (hhd : Commute h d)
    (hrel : h = a*b*a⁻¹*b⁻¹) (hrel2 : h*f = c*d*c⁻¹*d⁻¹) : False := by sorry
