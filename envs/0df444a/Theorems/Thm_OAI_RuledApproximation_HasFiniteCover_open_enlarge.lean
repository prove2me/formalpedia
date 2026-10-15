-- Prove2me | Theorems.Thm_OAI_RuledApproximation_HasFiniteCover_open_enlarge
-- name    : OAI.RuledApproximation.HasFiniteCover.open_enlarge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:53:30.387347+00:00
-- url     : https://prove2.me/theorems/2e988c32-1004-4c16-ad8c-712f4cf6dc99
-- title:
--   Parallelogram-cylinder covers enlarge to open bounded cylinder covers at arbitrarily small extra area
-- statement:
--   A *cylinder* $C$ in $\mathbb{R}^3$ is given by a unit vector $u$ (its axis) and a base set $B\subseteq u^{\perp}$ in the plane orthogonal to $u$. Its carrier is the infinite cylinder $\operatorname{car}(C)=\{b+tu : b\in B,\ t\in\mathbb{R}\}$, and its area $\operatorname{area}(C)$ is the two-dimensional Lebesgue measure of $B$ inside the plane $u^{\perp}$. It is a *parallelogram cylinder* if $B=\{c+sx+ty : s,t\in[0,1]\}$ for some $c,x,y\in u^{\perp}$ with $x,y$ linearly independent. It is an *open bounded cylinder* if its base $B$ is an open subset of the plane $u^\perp$ that is bounded and Lebesgue measurable.
--
--   **Theorem.** Let $S\subseteq\mathbb{R}^3$, $A\in\mathbb{R}$ and $\varepsilon>0$. If $S$ is covered by finitely many parallelogram cylinders $C_1,\dots,C_n$ with $\sum_i\operatorname{area}(C_i)\le A$, then $S$ is covered by finitely many open bounded cylinders $D_1,\dots,D_m$ with
--   $$
--   S\subseteq\bigcup_{j=1}^{m}\operatorname{car}(D_j),\qquad \sum_{j=1}^{m}\operatorname{area}(D_j)\le A+\varepsilon .
--   $$
--
--   The covering theorems for ruled sets are first proved with compact (closed parallelogram) bases. This lemma converts any such cover into one with open bounded bases at an arbitrarily small additional cost, and without discarding any part of the covered set; it is how the open-base forms of the main covering statements (the logarithmic and product-cell cases) are obtained from the parallelogram forms.
--
--   **Formalization Note** The statement is `HasFiniteCover Cylinder.parallelogram S A → 0 < eps → HasFiniteCover Cylinder.openBounded S (A + eps)`, where `Cylinder.openBounded C` means `IsOpen C.base ∧ Bornology.IsBounded C.base ∧ MeasurableSet C.base` in the subspace topology of the plane orthogonal to the axis.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/SpecializedCover.lean#L37-L59

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

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.HasFiniteCover.open_enlarge {S : Set Space} {A eps : ℝ}
    (hc : HasFiniteCover Cylinder.parallelogram S A) (heps : 0 < eps) :
    HasFiniteCover Cylinder.openBounded S (A+eps) := by sorry
