-- Prove2me | Theorems.Thm_OAI_ThreeManifold_Cometric_first_derivative_bound
-- name    : OAI.ThreeManifold.Cometric.first_derivative_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:23:15.186816+00:00
-- url     : https://prove2.me/theorems/f1b8b1a8-1474-43e7-b1fe-16eb3627da22
-- title:
--   First-derivative bound for the neck cometric in terms of an error bound $B$
-- statement:
--   Let $a(u)=e^{-1/(2/3-u)}$ for $u<2/3$ and $a(u)=0$ for $u\ge 2/3$; this is a smooth function with values in $[0,1)$. Let $\mathcal{A}(u)=\int_0^u a(y)\,dy$, and let $\chi(t)=\psi\bigl(6(t-5/12)\bigr)$, where $\psi$ is the standard smooth transition function ($C^\infty$, nondecreasing, $\psi=0$ on $(-\infty,0]$ and $\psi=1$ on $[1,\infty)$). So $\chi$ rises from $0$ to $1$ on $[5/12,7/12]$. For parameters $\delta,t\in\mathbb{R}$ put
--   $$
--   d_1=1+\delta\mathcal{A}(t),\qquad d_2=1+\delta\mathcal{A}(1-t),\qquad s=\delta^2\chi(t),\qquad
--   P(\delta,t)=\begin{pmatrix}d_1+d_2s^2 & d_2s\\ d_2s & d_2\end{pmatrix}.
--   $$
--
--   Let $u_1=\delta a(t)$, $u_2=-\delta a(1-t)$, $v=\delta^2\chi'(t)$, and let
--   $$
--   P_1(\delta,t)=\begin{pmatrix}u_1+u_2s^2+2d_2sv & u_2s+d_2v\\ u_2s+d_2v & u_2\end{pmatrix}
--   $$
--   be the $t$-derivative of $P(\delta,t)$. Let $N_1(\delta,t)$ be the symmetric matrix with entries
--   $$
--   N_1(\delta,t)_{00}=-\delta^3a(1-t)\chi(t)^2+2d_2\,\delta^2\chi(t)\chi'(t),\qquad
--   N_1(\delta,t)_{01}=N_1(\delta,t)_{10}=-\delta\,a(1-t)\chi(t)+d_2\,\chi'(t),
--   $$
--   and $N_1(\delta,t)_{11}=0$, so that $P_1=\mathrm{diag}(u_1,u_2)+\delta^2N_1$. Write $|p|^2=p_0^2+p_1^2$.
--
--   **Theorem.** Let $0\le\delta\le1/2$, $t\in\mathbb{R}$ and $B\ge0$, and suppose $|N_1(\delta,t)_{ij}|\le B$ for all $i,j$. Then for every $p\in\mathbb{R}^2$,
--   $$
--   |P_1(\delta,t)\,p|^2\le(2+8B^2)\,\delta^2\,|p|^2 .
--   $$
--
--   So the $t$-derivative of the cometric is of order $\delta$, with a constant that depends only on a bound for the normalized error matrix $N_1$. Together with a compactness bound on $N_1$, this gives the uniform first-derivative estimate for the neck cometric.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Neck.lean#L1190-L1204

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

theorem OAI.ThreeManifold.Cometric.first_derivative_bound {δ t B : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (hB : 0 ≤ B)
    (hN : ∀ i j, |N₁ δ t i j| ≤ B) (p : V2) :
    sqnorm (P₁ δ t *ᵥ p) ≤ (2 + 8 * B ^ 2) * δ ^ 2 * sqnorm p := by sorry
