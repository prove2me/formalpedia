-- Prove2me | Theorems.Thm_OAI_ThreeManifold_Neck_boundaryTerm_hasDerivAt
-- name    : OAI.ThreeManifold.Neck.boundaryTerm_hasDerivAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:15:04.80772+00:00
-- url     : https://prove2.me/theorems/08167530-09b7-444c-b67b-3ee590a269af
-- title:
--   Derivative of the boundary term along a geodesic of $dt^2+Q(t)$
-- statement:
--   For a real $2\times 2$ matrix $A$ and $u,v\in\mathbb{R}^2$ write $\langle u,v\rangle_A = u^{\mathsf T}Av$. Elements of $\mathbb{R}\times\mathbb{R}^2$ are written $U=(U^0,\bar U)$ with $U^0\in\mathbb{R}$ and $\bar U\in\mathbb{R}^2$. For a $2\times2$ matrix $A$ define the boundary term
--   $$
--   \beta_A(T,V)=-\tfrac12\,T^0\langle\bar V,\bar V\rangle_A+V^0\langle\bar T,\bar V\rangle_A ,
--   $$
--   and for $2\times2$ matrices $P,A,B$ define the boundary jet $b_{P,A,B}(T,V,\dot V)$ by
--
--   $$
--   \begin{aligned}
--   b_{P,A,B}(T,V,\dot V) ={}& -\tfrac14\langle\bar T,\bar T\rangle_A\langle\bar V,\bar V\rangle_A - T^0\langle\dot{\bar V},\bar V\rangle_A - \tfrac12 (T^0)^2\langle\bar V,\bar V\rangle_B \\
--   &+ \dot V^0\langle\bar V,\bar T\rangle_A + V^0\langle\dot{\bar V},\bar T\rangle_A + V^0T^0\langle\bar V,\bar T\rangle_B - V^0T^0\langle\bar V,\bar T\rangle_{APA}.
--   \end{aligned}
--   $$
--
--   **Theorem.** Let $A:\mathbb{R}\to\mathbb{R}^{2\times2}$, $t,v,w:\mathbb{R}\to\mathbb{R}$, $u,z:\mathbb{R}\to\mathbb{R}^2$, let $P,B$ be $2\times2$ matrices, $w'\in\mathbb{R}$, $z'\in\mathbb{R}^2$ and $s\in\mathbb{R}$. Assume:
--
--   1. $P$, $B$ and $A(t(s))$ are symmetric;
--   2. $A$ is differentiable at $t(s)$ with derivative $B$;
--   3. $t$ is differentiable at $s$ with $t'(s)=v(s)$;
--   4. $v$ is differentiable at $s$ with $v'(s)=\tfrac12\langle u(s),u(s)\rangle_{A(t(s))}$;
--   5. $u$ is differentiable at $s$ with $u'(s)=-v(s)\,P\,A(t(s))\,u(s)$;
--   6. $w$ and $z$ are differentiable at $s$ with $w'(s)=w'$ and $z'(s)=z'$.
--
--   Then $r\mapsto\beta_{A(t(r))}\bigl((v(r),u(r)),(w(r),z(r))\bigr)$ is differentiable at $s$, and
--   $$
--   \frac{d}{dr}\Big|_{r=s}\beta_{A(t(r))}\bigl((v(r),u(r)),(w(r),z(r))\bigr)=b_{P,\,A(t(s)),\,B}\bigl((v(s),u(s)),\,(w(s),z(s)),\,(w',z')\bigr).
--   $$
--
--   Conditions 3 to 5 are the geodesic equations, at the parameter $s$, of the metric $dt^2+Q(t)_{ij}dx^idx^j$ when $A=\partial_tQ$ and $P=Q(t(s))^{-1}$: $(v,u)$ is the velocity of the geodesic. The lemma identifies the term $b$ in the pointwise index-form identity as an exact derivative. This is what allows the integrated index form to be written as an energy integral plus boundary values.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Neck.lean#L299-L318

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck

open OAI OAI.ThreeManifold OAI.ThreeManifold.Neck
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Matrix
open scoped Matrix Matrix.Norms.Elementwise

theorem OAI.ThreeManifold.Neck.boundaryTerm_hasDerivAt {A : ℝ → TMat} {t v w : ℝ → ℝ} {u z : ℝ → TVec}
    {P B : TMat} {w' : ℝ} {z' : TVec} {s : ℝ}
    (hP : Pᵀ = P) (hAs : (A (t s))ᵀ = A (t s)) (hB : Bᵀ = B)
    (hA : HasDerivAt A B (t s)) (ht : HasDerivAt t (v s) s)
    (hv : HasDerivAt v ((1 / 2 : ℝ) * pairing (A (t s)) (u s) (u s)) s)
    (hu : HasDerivAt u (-v s • (P *ᵥ (A (t s) *ᵥ u s))) s)
    (hw : HasDerivAt w w' s) (hz : HasDerivAt z z' s) :
    HasDerivAt (fun r => boundaryTerm (A (t r)) (v r, u r) (w r, z r))
      (boundaryJet P (A (t s)) B (v s, u s) (w s, z s) (w', z')) s := by sorry
