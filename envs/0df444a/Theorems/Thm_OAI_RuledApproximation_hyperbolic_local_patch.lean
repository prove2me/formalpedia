-- Prove2me | Theorems.Thm_OAI_RuledApproximation_hyperbolic_local_patch
-- name    : OAI.RuledApproximation.hyperbolic_local_patch
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:50:11.803901+00:00
-- url     : https://prove2.me/theorems/52d735c6-cd01-40e1-8721-29cf594daa79
-- title:
--   Each hyperbolic point has a patch admitting parallelogram covers with arbitrarily small area inflation
-- statement:
--   For $h,L\in\mathbb{R}$, $Q\subseteq\mathbb{R}^2$ and $v:\mathbb{R}^2\to\mathbb{R}^2$ let
--   $$
--   \mathcal R_h(Q,v,L)=\{(s,\ p_1+s\,v_1(p),\ h(p_2+s\,v_2(p))):\ p\in Q,\ |s|\le L\}\subseteq\mathbb{R}^3
--   $$
--   and $\omega_h(w)=1/\sqrt{1+w_1^2+h^2w_2^2}$ for $w\in\mathbb{R}^2$. A set $X\subseteq\mathbb{R}^3$ has a *finite parallelogram cover of cost at most* $C$ if finitely many cylinders, each with a unit axis $u$ and a parallelogram base in the plane $u^\perp$, have carriers covering $X$ and areas (two-dimensional Lebesgue measures of the bases) summing to at most $C$. A field $v$ is *$L$-hyperbolic at $p$* if its derivative $Dv(p)$ has real eigenvalues $\lambda$ and $-\lambda$ for some $\lambda$ with $0<L\lambda<1$.
--
--   Let $h>0$, $L>0$ and $B>1$. Let $U\subseteq\mathbb{R}^2$ be open, let $v:\mathbb{R}^2\to\mathbb{R}^2$ be $C^1$ on $U$, and let $p\in U$ be a point at which $v$ is $L$-hyperbolic. Then there is an open set $V$ containing $p$ such that for every compact $K\subseteq V$ and every $\varepsilon>0$, the set $\mathcal R_h(K,v,L)$ has a finite parallelogram cover of cost at most
--   $$
--   h\,B\int_K\omega_h\bigl(v(q)\bigr)\,dq+\varepsilon.
--   $$
--
--   The inflation factor $B>1$ is prescribed in advance and may be arbitrarily close to $1$; the patch $V$ depends on it. Combined with the globalization over compact label sets, this is the local input for the physical hyperbolic covering statement, whose bound is $h\int_D\omega_h(v)+\varepsilon$.
--
--   **Formalization Note** Hyperbolicity is `HyperbolicAt L v p`, stated with `Module.End.HasEigenvalue` for `fderiv ℝ v p`; the integral is over `Plane` (the type `EuclideanSpace ℝ (Fin 2)`) with Lebesgue measure, and covers are `HasFiniteCover Cylinder.parallelogram`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/HyperbolicCover.lean#L186-L251

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.hyperbolic_local_patch {h L B : ℝ} (hh : 0 < h) (hL : 0 < L) (hB : 1 < B)
    {v : Plane → Plane} {U : Set Plane} (hU : IsOpen U) (hv : ContDiffOn ℝ 1 v U)
    {p : Plane} (hp : p ∈ U) (hhyp : HyperbolicAt L v p) :
    ∃ V : Set Plane, IsOpen V ∧ p ∈ V ∧ ∀ K : Set Plane, IsCompact K → K ⊆ V →
      ∀ eps : ℝ, 0 < eps → HasFiniteCover Cylinder.parallelogram (physicalRuled h K v L)
        (h * B * (∫ q in K, physicalWeight h (v q)) + eps) := by sorry
