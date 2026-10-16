-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_stationaryMotionField_realizes
-- name    : OAI.BoxTransport.Routing.stationaryMotionField_realizes
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T13:18:52.880334+00:00
-- url     : https://prove2.me/theorems/95b23f91-ff79-4946-b5e4-ed765bd9b19d
-- title:
--   Smooth separated volume-preserving box motions are realized exactly by a divergence-free curl field
-- statement:
--   Let $n\in\mathbb{N}$, and for each box $i\in\{1,\dots,n\}$ let $a_i,h_i\in\mathbb{R}^3$ (initial center and half-widths) and let $c_i,d_i:\mathbb{R}\to\mathbb{R}^3$ be curves (the path of the center and the diagonal stretching factors). Let $\eta>0$ and $M>0$. For $u,w\in\mathbb{R}^3$ write $u\odot w=(u_1w_1,u_2w_2,u_3w_3)$, $\mathbf 1=(1,1,1)$ and $B(c,r)=\{x\in\mathbb{R}^3:|x_j-c_j|\le r_j,\ j=1,2,3\}$. Assume:
--
--   1. every $c_i$ and every $d_i$ is $C^\infty$;
--   2. $c_i(t)=a_i$ and $d_i(t)=\mathbf 1$ for all $t\le 1/4$;
--   3. $c_i(t)=c_i(1)$ and $d_i(t)=d_i(1)$ for all $t\ge 3/4$;
--   4. $d_{i1}(t)\,d_{i2}(t)\,d_{i3}(t)=1$ for all $t$;
--   5. $0<d_{ij}(t)\le M$ for all $i$, $j$, $t$;
--   6. for every $t$, the padded boxes $B\big(c_i(t),\,d_i(t)\odot h_i+2\eta\mathbf 1\big)$, $i=1,\dots,n$, are pairwise disjoint.
--
--   **The field.** Let $S(y)=\psi(y)/(\psi(y)+\psi(1-y))$ be the smooth transition function, where $\psi(y)=e^{-1/y}$ for $y>0$ and $\psi(y)=0$ for $y\le0$. Put $r_i(t)=d_i(t)\odot h_i$, $v_i=c_i'$, $\ell_{ij}=d_{ij}'/d_{ij}$ and, for box $i$, $y=x-c_i(t)$. The cutoff and the quadratic potential of box $i$ are
--
--   $$\chi_i(t,x)=\prod_{j=1}^3S\Big(\frac{r_{ij}(t)+2\eta+y_j}{\eta}\Big)S\Big(\frac{r_{ij}(t)+2\eta-y_j}{\eta}\Big),\qquad A_i=\big(P^i_{23},P^i_{31},P^i_{12}\big),$$
--
--   $$P^i_{jk}(t,x)=\tfrac12\big(v_{ij}(t)\,y_k-v_{ik}(t)\,y_j\big)+\tfrac13\big(\ell_{ij}(t)-\ell_{ik}(t)\big)\,y_j\,y_k,$$
--
--   and the velocity field is $U=\operatorname{curl}_x\big(\sum_{i=1}^n\chi_iA_i\big)$, where $\operatorname{curl}_xA=(\partial_2A_3-\partial_3A_2,\ \partial_3A_1-\partial_1A_3,\ \partial_1A_2-\partial_2A_1)$ and $\partial_j=\partial/\partial x_j$.
--
--   **Theorem.** Under these assumptions:
--
--   1. $U$ is $C^\infty$ on $\mathbb{R}\times\mathbb{R}^3$;
--   2. $U$ has compact support;
--   3. $U$ is divergence free in space: $\sum_{j=1}^3\partial_jU_j(t,x)=0$ for all $(t,x)$;
--   4. $U(t,x)=0$ whenever $t\notin[1/4,3/4]$;
--   5. there is a global flow $\Phi$ of $U$ (that is, $\Phi(0,x)=x$, $\partial_t\Phi(t,x)=U(t,\Phi(t,x))$ for all $t$, and every curve $\gamma$ with $\gamma(0)=x$ and $\gamma'(t)=U(t,\gamma(t))$ for all $t$ equals $\Phi(\cdot,x)$) such that for every $i$ there is an open set $O_i\supseteq B(a_i,h_i)$ with
--
--   $$\Phi(t,x)=c_i(t)+d_i(t)\odot(x-a_i)\qquad\text{for all } x\in O_i \text{ and all } t\in\mathbb{R}.$$
--
--   Any smooth motion of finitely many boxes by translations and volume-preserving diagonal stretchings that keeps the padded boxes disjoint and is stationary outside $[1/4,3/4]$ is therefore realized exactly, on a neighbourhood of each initial box, by the flow of an explicit smooth, compactly supported, incompressible velocity field. The balanced box-routing theorem is obtained by applying this to an explicit five-stage motion of rational boxes and reading off the flow at time $1$.
--
--   **Formalization Note** The field is `stationaryMotionField c d h η`, i.e. `spatialCurl` of `familyPotential` with velocities `deriv (c i)`, logarithmic velocities `diagonalLogVelocity (d i)` and radii `fun i t j => d i t j * h i j`. Coordinates are indexed by `Fin 3` and boxes by `Fin n`. The half-widths $h_i$ are not required to be nonnegative (a negative entry makes $B(a_i,h_i)$ empty). The divergence is `spatialDivergence`, computed from the derivative of the time slice $y\mapsto U(t,y)$, and the flow property is `IsGlobalFlow`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Motion.lean#L516-L578

import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion

open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff

theorem OAI.BoxTransport.Routing.stationaryMotionField_realizes {n : ℕ}
    (a h : Fin n → Space) {c d : Fin n → ℝ → Space}
    {η M : ℝ} (hη : 0 < η) (hM : 0 < M)
    (hc : ∀ i, ContDiff ℝ ∞ (c i)) (hd : ∀ i, ContDiff ℝ ∞ (d i))
    (hstart : ∀ i t, t ≤ (1 / 4 : ℝ) → c i t = a i ∧ d i t = 1)
    (hend : ∀ i t, (3 / 4 : ℝ) ≤ t → c i t = c i 1 ∧ d i t = d i 1)
    (hdet : ∀ i t, ∏ j : Fin 3, d i t j = 1)
    (hdpos : ∀ i t j, 0 < d i t j) (hdM : ∀ i t j, d i t j ≤ M)
    (hdis : ∀ t, Pairwise fun i j =>
      Disjoint (realBox (c i t) (fun k => d i t k * h i k + 2 * η))
        (realBox (c j t) (fun k => d j t k * h j k + 2 * η))) :
    ContDiff ℝ ∞ (stationaryMotionField c d h η) ∧
    HasCompactSupport (stationaryMotionField c d h η) ∧
    (∀ t x, spatialDivergence (stationaryMotionField c d h η) t x = 0) ∧
    (∀ (t : ℝ) x, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) →
      stationaryMotionField c d h η (t, x) = 0) ∧
    ∃ Φ, IsGlobalFlow (stationaryMotionField c d h η) Φ ∧
      (∀ i, ∃ O : Set Space, IsOpen O ∧ realBox (a i) (h i) ⊆ O ∧
        ∀ x ∈ O, ∀ t, Φ t x = affineTrajectory (c i) (d i) (a i) x t) := by sorry
