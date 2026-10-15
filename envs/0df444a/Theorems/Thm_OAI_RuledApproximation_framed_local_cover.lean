-- Prove2me | Theorems.Thm_OAI_RuledApproximation_framed_local_cover
-- name    : OAI.RuledApproximation.framed_local_cover
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:48:50.483384+00:00
-- url     : https://prove2.me/theorems/3260d234-53ab-44b5-a7f0-4131e496f02f
-- title:
--   Finite parallelogram-cylinder cover of a ruled patch from a lattice model in a linear frame
-- statement:
--   **Setting.** A *cylinder* in $\mathbb{R}^3$ is given by a unit vector $u$ (its axis) and a base $B$ contained in the plane $u^\perp$; its carrier is $\{b+tu:\ b\in B,\ t\in\mathbb{R}\}$ and its area is the two-dimensional Lebesgue measure of $B$ in $u^\perp$. It is a *parallelogram cylinder* if $B=\{c+s\,a_1+t\,a_2:\ s,t\in[0,1]\}$ for some $c$ and some linearly independent $a_1,a_2$ in $u^\perp$. A set $X\subseteq\mathbb{R}^3$ has a *finite parallelogram cover of cost at most* $C$ if finitely many parallelogram cylinders have carriers covering $X$ and areas summing to at most $C$. For $h,L\in\mathbb{R}$, $Q\subseteq\mathbb{R}^2$ and $v:\mathbb{R}^2\to\mathbb{R}^2$ put
--   $$
--   \mathcal R_h(Q,v,L)=\{(s,\ p_1+s\,v_1(p),\ h(p_2+s\,v_2(p))):\ p\in Q,\ |s|\le L\}\subseteq\mathbb{R}^3
--   $$
--   and $\omega_h(w)=1/\sqrt{1+w_1^2+h^2w_2^2}$ for $w\in\mathbb{R}^2$. Finally, for a linear map $A$ of $\mathbb{R}^2$, the triple $(A,L,R)$ is a *lattice model* if for every integer $n\ge1$, every $p\in\mathbb{R}^2$ and every $r$ with $|r|\le L$ there is $b\in\tfrac1n\mathbb{Z}^2$ with $\|b-p\|_\infty\le R/n$ and $\|(p-b)+rA(p-b)\|_\infty\le\frac1{2n}$.
--
--   **Statement.** Let $M:\mathbb{R}^2\to\mathbb{R}^2$ be an invertible linear map from the coordinate plane (with the maximum norm $\|\cdot\|_\infty$) to the Euclidean plane, and let $h>0$, $L\ge0$, $R\ge0$, $\delta\ge0$. Let $K\subseteq U$ be subsets of the coordinate plane with $K$ compact and $U$ open, let $v:\mathbb{R}^2\to\mathbb{R}^2$ be any map, and let $A$ be a linear map of the coordinate plane such that $(A,L,R)$ is a lattice model and the field read in the frame $M$ satisfies
--   $$
--   \|M^{-1}v(Mp)-M^{-1}v(Mb)-A(p-b)\|_\infty\le\delta\,\|p-b\|_\infty\qquad\text{for all } p,b\in U.
--   $$
--   Let $F:\mathbb{R}^2\to\mathbb{R}$ be continuous with $F\ge0$ and $F(p)=\omega_h(v(Mp))$ for all $p\in U$, and let $\varepsilon>0$. Then $\mathcal R_h(M(K),v,L)$ has a finite parallelogram cover of cost at most
--   $$
--   h\,(1+2L\delta R)^2\int_{M(K)}\omega_h\bigl(v(q)\bigr)\,dq+\varepsilon.
--   $$
--
--   When $A$ is the normal form of the derivative of $v$ at a point and $\delta$ is small, the inflation factor $(1+2L\delta R)^2$ is close to $1$, so this is the local form of the bound $h\int\omega_h(v)+\varepsilon$ in the physical hyperbolic covering statement. The auxiliary function $F$ only serves to have a weight that is continuous on the whole coordinate plane.
--
--   **Formalization Note** $M$ is a continuous linear equivalence `Coordinates ≃L[ℝ] Plane`; norms on `Coordinates` (the type `Fin 2 → ℝ`) are sup norms. The ruled set is `physicalRuled h (M '' K) v L`, the weight is `physicalWeight h`, the conclusion is `HasFiniteCover Cylinder.parallelogram`, and a cylinder's area is the real number `volume.real` of its base.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/LocalCover.lean#L26-L96

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.framed_local_cover (M : Coordinates ≃L[ℝ] Plane) {h L R delta : ℝ}
    (hh : 0 < h) (hL : 0 ≤ L) (hR : 0 ≤ R) (hd : 0 ≤ delta)
    {K U : Set Coordinates} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (v : Plane → Plane) (A : Coordinates →L[ℝ] Coordinates)
    (hmodel : LatticeModel A L R)
    (hrem : ∀ p ∈ U, ∀ b ∈ U,
      ‖M.symm (v (M p)) - M.symm (v (M b)) - A (p - b)‖ ≤ delta * ‖p - b‖)
    {F : Coordinates → ℝ} (hF : Continuous F) (hFpos : ∀ p, 0 ≤ F p)
    (hFval : ∀ p ∈ U, F p = physicalWeight h (v (M p)))
    {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover Cylinder.parallelogram (physicalRuled h (M '' K) v L)
      (h * (1 + 2 * L * delta * R) ^ 2 *
        (∫ p in M '' K, physicalWeight h (v p)) + eps) := by sorry
