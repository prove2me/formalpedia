-- Prove2me | Theorems.Thm_OAI_ThreeManifold_Cometric_P_hasDerivAt
-- name    : OAI.ThreeManifold.Cometric.P_hasDerivAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:18:31.29989+00:00
-- url     : https://prove2.me/theorems/f47f30d2-f8da-406e-8157-77d499ac0d7c
-- title:
--   Derivative in $t$ of the neck cometric $P(\delta,t)$
-- statement:
--   Let $a(u)=e^{-1/(2/3-u)}$ for $u<2/3$ and $a(u)=0$ for $u\ge 2/3$; this is a smooth function with values in $[0,1)$. Let $\mathcal{A}(u)=\int_0^u a(y)\,dy$, and let $\chi(t)=\psi\bigl(6(t-5/12)\bigr)$, where $\psi$ is the standard smooth transition function ($C^\infty$, nondecreasing, $\psi=0$ on $(-\infty,0]$ and $\psi=1$ on $[1,\infty)$). So $\chi$ rises from $0$ to $1$ on $[5/12,7/12]$. For parameters $\delta,t\in\mathbb{R}$ put
--   $$
--   d_1=1+\delta\mathcal{A}(t),\qquad d_2=1+\delta\mathcal{A}(1-t),\qquad s=\delta^2\chi(t),\qquad
--   P(\delta,t)=\begin{pmatrix}d_1+d_2s^2 & d_2s\\ d_2s & d_2\end{pmatrix}.
--   $$
--
--   Write also $u_1=\delta\,a(t)$, $u_2=-\delta\,a(1-t)$, $v=\delta^2\chi'(t)$, and
--   $$
--   P_1(\delta,t)=\begin{pmatrix}u_1+u_2s^2+2d_2sv & u_2s+d_2v\\ u_2s+d_2v & u_2\end{pmatrix}.
--   $$
--
--   **Theorem.** For all $\delta,t\in\mathbb{R}$, the matrix-valued function $\tau\mapsto P(\delta,\tau)$ is differentiable at $t$, with
--   $$
--   \frac{\partial}{\partial t}P(\delta,t)=P_1(\delta,t).
--   $$
--
--   The functions $u_1,u_2,v$ are the $t$-derivatives of $d_1,d_2,s$. This explicit first derivative feeds the derivative and concavity estimates for the neck cometric.
--
--   **Formalization Note** Differentiability of a $2\times2$-matrix-valued function is with respect to the entrywise sup norm, which is equivalent to entrywise differentiability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Neck.lean#L918-L932

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck

open OAI OAI.ThreeManifold OAI.ThreeManifold.Cometric
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Matrix
open scoped Matrix.Norms.Elementwise

theorem OAI.ThreeManifold.Cometric.P_hasDerivAt (δ t : ℝ) : HasDerivAt (P δ) (P₁ δ t) t := by sorry
