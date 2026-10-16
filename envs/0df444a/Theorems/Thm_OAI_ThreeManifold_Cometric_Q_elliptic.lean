-- Prove2me | Theorems.Thm_OAI_ThreeManifold_Cometric_Q_elliptic
-- name    : OAI.ThreeManifold.Cometric.Q_elliptic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:19:34.133546+00:00
-- url     : https://prove2.me/theorems/cb63be5c-dbc3-4dd6-b509-a6ebe9d1836b
-- title:
--   Uniform ellipticity of the neck metric $Q(\delta,t)=P(\delta,t)^{-1}$
-- statement:
--   Let $a(u)=e^{-1/(2/3-u)}$ for $u<2/3$ and $a(u)=0$ for $u\ge 2/3$; this is a smooth function with values in $[0,1)$. Let $\mathcal{A}(u)=\int_0^u a(y)\,dy$, and let $\chi(t)=\psi\bigl(6(t-5/12)\bigr)$, where $\psi$ is the standard smooth transition function ($C^\infty$, nondecreasing, $\psi=0$ on $(-\infty,0]$ and $\psi=1$ on $[1,\infty)$). So $\chi$ rises from $0$ to $1$ on $[5/12,7/12]$. For parameters $\delta,t\in\mathbb{R}$ put
--   $$
--   d_1=1+\delta\mathcal{A}(t),\qquad d_2=1+\delta\mathcal{A}(1-t),\qquad s=\delta^2\chi(t),\qquad
--   P(\delta,t)=\begin{pmatrix}d_1+d_2s^2 & d_2s\\ d_2s & d_2\end{pmatrix}.
--   $$
--
--   For $p\in\mathbb{R}^2$ write $|p|^2=p_0^2+p_1^2$, and for a $2\times2$ matrix $M$ write $q_M(p)=p^{\mathsf T}Mp$. Let $Q(\delta,t)=P(\delta,t)^{-1}$.
--
--   **Theorem.** If $0\le\delta\le 1/2$ and $0\le t\le1$, then for every $p\in\mathbb{R}^2$
--   $$
--   \frac{|p|^2}{6}\le q_{Q(\delta,t)}(p)\le 3\,|p|^2 .
--   $$
--
--   $Q(\delta,t)$ is the flat metric on the torus fibres of the neck that is dual to the cometric $P(\delta,t)$. The bounds are uniform in $\delta$ and $t$, and match the ellipticity constants of $P$.
--
--   **Formalization Note** $Q$ is defined with Lean's matrix inverse, which is total. Here $\det P=d_1d_2\ge1$, so it is the genuine inverse.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Neck.lean#L977-L1001

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

theorem OAI.ThreeManifold.Cometric.Q_elliptic {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) (p : V2) :
    sqnorm p / 6 ≤ qform (Q δ t) p ∧ qform (Q δ t) p ≤ 3 * sqnorm p := by sorry
