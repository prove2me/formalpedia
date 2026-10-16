-- Prove2me | Theorems.Thm_OAI_ThreeManifold_GluedConstruction_gluing_transition_positive
-- name    : OAI.ThreeManifold.GluedConstruction.gluing_transition_positive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:09:51.247353+00:00
-- url     : https://prove2.me/theorems/3a06b48b-914e-45ce-8259-629bbad41934
-- title:
--   The two-piece gluing map is orientation-preserving in charts
-- statement:
--   Let $\mathbb{H}=\{z\in\mathbb{C}:\operatorname{Im}z>0\}$, let $\Sigma=\mathbb{H}/\overline{\Gamma}$ be the cusped hyperbolic surface of the construction (the quotient of $\mathbb{H}$ by a fixed torsion-free group of Möbius transformations coming from $SL(2,\mathbb{Z})$) with covering projection $\pi:\mathbb{H}\to\Sigma$ and height function $\mathrm{ht}:\Sigma\to\mathbb{R}$, where $\mathrm{ht}(\pi(z))=\log\operatorname{Im}z$ whenever $\operatorname{Im}z>1$. Put $\Sigma_8=\{q\in\Sigma:\mathrm{ht}(q)<\log 8\}$ and $S^1_6=\mathbb{R}/6\mathbb{Z}$, and let the *piece* be the 3-manifold $X=\Sigma_8\times S^1_6$, modelled on $\mathbb{C}\times\mathbb{R}\cong\mathbb{R}^3$. For $a\in X$ let $\varphi_a$ be the preferred chart of $X$ at $a$: the product of the surface chart at the first component (a local inverse branch of $\pi$, read in $\mathbb{H}\subset\mathbb{C}$) and the circle chart at the second component (a local inverse of $\mathbb{R}\to S^1_6$).
--
--   The *collar* $O\subset X$ is the open set of points whose surface component lies in the cusp $\pi(\{\operatorname{Im}z>2\})$; its points are exactly $(\pi(z),\,r \bmod 6)$ with $2<\operatorname{Im}z<8$ and $r\in\mathbb{R}$. The gluing homeomorphism $\Phi:O\to O$ is given in the cusp coordinates $(y,\,x \bmod 6,\,r\bmod 6)$, $y=\operatorname{Im}z$, $x=\operatorname{Re}z$, by
--   $$
--   \Phi(y,\,x,\,r)=\Bigl(\frac{16}{y},\ r,\ x-r\Bigr),
--   $$
--   and $\tilde\Phi:X\to X$ denotes its extension by the identity outside $O$. The closed manifold of the construction is obtained from two copies of $X$ by identifying $p\in O$ in the first copy with $\Phi(p)$ in the second.
--
--   **Theorem.** Let $a,b\in X$ and $x\in\mathbb{C}\times\mathbb{R}$ with $x$ in the target of $\varphi_a$, $\varphi_a^{-1}(x)\in O$, and $\tilde\Phi(\varphi_a^{-1}(x))$ in the source of $\varphi_b$. Then the real Jacobian determinant of the coordinate transition $y\mapsto \varphi_b(\tilde\Phi(\varphi_a^{-1}(y)))$ at $x$ is positive:
--   $$
--   \det D\bigl(\varphi_b\circ\tilde\Phi\circ\varphi_a^{-1}\bigr)(x)>0 .
--   $$
--
--   In words, the gluing map is orientation-preserving with respect to the preferred charts of the piece. Together with the positivity of the transition maps inside each copy of $X$, this is what makes the atlas of the glued closed 3-manifold oriented.
--
--   **Formalization Note** The derivative is the real Fréchet derivative of a map $\mathbb{C}\times\mathbb{R}\to\mathbb{C}\times\mathbb{R}$, and its determinant is taken as a linear endomorphism of this 3-dimensional real space. Charts are total functions in Lean, so the composite is defined everywhere; the hypotheses guarantee that near $x$ it is a genuine transition map. The extension $\tilde\Phi$ is `extendedTransition collar gluingMap`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Gluing.lean#L1325-L1376

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing

open OAI OAI.ThreeManifold OAI.ThreeManifold.GluedConstruction
open Set Manifold Bundle
open scoped ContDiff
open Set Filter Topology Manifold
open scoped ContDiff
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Set Pointwise
open Matrix Set Manifold
open scoped MatrixGroups UpperHalfPlane ContDiff
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix Set Manifold
open scoped MatrixGroups UpperHalfPlane ContDiff
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups
open Set Topology TopologicalSpace CategoryTheory
open Set Topology TopologicalSpace
open Set Topology Filter Manifold
open scoped ContDiff
open Set Topology Filter Manifold TopologicalSpace
open scoped ContDiff UpperHalfPlane MatrixGroups
open Set Topology Filter TopologicalSpace Manifold IsManifold
open scoped ContDiff
open Set Topology Filter Manifold TopologicalSpace
open scoped ContDiff
open Set Topology Filter Manifold IsManifold
open scoped ContDiff
open Set Filter Topology Manifold IsManifold
open scoped ContDiff
open Set Filter Topology Manifold Matrix
open scoped ContDiff UpperHalfPlane MatrixGroups
open Set Filter Topology Manifold IsManifold
open scoped ContDiff
open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
open Set Filter Topology
open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
open HyperbolicCore Coordinates3 TwoGluing

theorem OAI.ThreeManifold.GluedConstruction.gluing_transition_positive (a b : Piece) (x : ℂ × ℝ)
    (hx : x ∈ (chartAt (ℂ × ℝ) a).target)
    (hO : (chartAt (ℂ × ℝ) a).symm x ∈ collar)
    (hb : extendedTransition collar gluingMap ((chartAt (ℂ × ℝ) a).symm x) ∈
      (chartAt (ℂ × ℝ) b).source) :
    0 < LinearMap.det (fderiv ℝ
      (fun y => chartAt (ℂ × ℝ) b
        (extendedTransition collar gluingMap ((chartAt (ℂ × ℝ) a).symm y))) x).toLinearMap := by sorry
