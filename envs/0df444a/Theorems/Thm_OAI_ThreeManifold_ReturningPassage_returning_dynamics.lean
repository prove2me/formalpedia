-- Prove2me | Theorems.Thm_OAI_ThreeManifold_ReturningPassage_returning_dynamics
-- name    : OAI.ThreeManifold.ReturningPassage.returning_dynamics
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:32:47.182005+00:00
-- url     : https://prove2.me/theorems/444289d4-5e5d-4b74-be92-3ad1bc124c04
-- title:
--   Shape of a returning passage: symmetry, turning point, convexity and $\int_0^L v^2 \le L v(0)^2/3$
-- statement:
--   Let $a(u) = e^{-1/(2/3-u)}$ for $u < 2/3$ and $a(u) = 0$ for $u \ge 2/3$ (a smooth cutoff), let $A(u) = \int_0^u a(y)\,dy$, and let $\chi(t) = \sigma\big(6(t - 5/12)\big)$ be a smooth step, where $\sigma(x) = \psi(x)/(\psi(x) + \psi(1-x))$ and $\psi(x) = e^{-1/x}$ for $x > 0$, $\psi(x) = 0$ for $x \le 0$. For a real parameter $\delta$ put $d_1(t) = 1 + \delta A(t)$, $d_2(t) = 1 + \delta A(1-t)$, $\eta(t) = \delta^2 \chi(t)$ and
--   $$
--   P_\delta(t) = \begin{pmatrix} d_1(t) + d_2(t)\,\eta(t)^2 & d_2(t)\,\eta(t) \\ d_2(t)\,\eta(t) & d_2(t) \end{pmatrix}, \qquad \widetilde P_\delta(t) = C_\delta\, P_\delta(1-t)\, C_\delta^{\top}, \qquad C_\delta = \begin{pmatrix} 0 & 1 \\ 1 & -\delta^2 \end{pmatrix}.
--   $$
--   The *coordinate cometric* $R_\delta = R^{\rho}_\delta : \mathbb{R} \to \mathbb{R}^{2 \times 2}$ with end flag $\rho \in \{\text{left}, \text{right}\}$ is $R^{\text{left}}_\delta = P_\delta$ and $R^{\text{right}}_\delta = \widetilde P_\delta$; it is a smooth family of symmetric matrices, and $R_\delta'$, $R_\delta''$ denote its first and second derivatives in $t$.
--
--   Fix an end flag $\rho$, $\delta \in \mathbb{R}$ and $p \in \mathbb{R}^2$, write $R = R^\rho_\delta$, and define the potential and the force
--   $$
--   V(u) = p^{\top} R(u)\, p, \qquad F(u) = p^{\top} R'(u)\, p = V'(u).
--   $$
--
--   **Theorem.** Let $L > 0$ and $t, v : \mathbb{R} \to \mathbb{R}$. Assume
--   - $q^{\top}\big(-R''(u)\big) q \ge 0$ for all $u \in [0,1]$ and $q \in \mathbb{R}^2$;
--   - $t' = v$ and $v' = -\tfrac12 F(t)$ at every point of $[0,L]$;
--   - $t(0) = 0$, $t(L) = 0$, and $t(s) \in (0,1)$ for every $s \in (0,L)$;
--   - (energy) $V(t(s)) + v(s)^2 = 1$ for every $s \in [0,L]$.
--
--   Put $T = t(L/2)$. Then:
--   1. $v(0) > 0$ and $v(L/2) = 0$;
--   2. $0 < T < 1$ and $t(s) \in [0,T]$ for all $s \in [0,L]$;
--   3. $t(L - s) = t(s)$ and $v(L - s) = -v(s)$ for all $s \in [0,L]$;
--   4. $F(u) > 0$ for every $u \in [0,T]$;
--   5. $v$ is convex and $t$ is concave on $[0, L/2]$;
--   6. the kinetic integral satisfies
--   $$
--   \int_0^L v(s)^2\, ds \le \frac{L\, v(0)^2}{3}.
--   $$
--
--   Here $t$ is the depth coordinate of a trajectory that enters the region $[0,1]$ at time $0$ and leaves it at time $L$, moving under the reduced equation of motion with conserved energy $1$. The theorem pins down the shape of such a returning passage (a single symmetric excursion with turning point at the midpoint), which is what the later index estimates for returning geodesics need.
--
--   **Formalization Note** `coordinateCometric right δ` is $R^{\rho}_\delta$ (`right = false` gives $P_\delta$ = `Cometric.P δ`, `right = true` gives `PEnd δ`); `pairing Q u v` $= u^{\top}Qv$, `qform Q q` $= q^{\top}Qq$, `sqnorm q` $= q_1^2+q_2^2$; Lean indexes the coordinates of $p$ as `p 0`, `p 1`, so $p_1$ is `p 0`. Derivatives are Lean's `deriv`, which are genuine derivatives here because $R_\delta$ is smooth. The force is `force right δ p` and the potential is `potential right δ p`; convexity and concavity are `ConvexOn ℝ (Icc 0 (L/2))` and `ConcaveOn ℝ (Icc 0 (L/2))`, and the integral is an interval integral.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Returning.lean#L1234-L1282

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning

open OAI OAI.ThreeManifold OAI.ThreeManifold.ReturningPassage
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set MeasureTheory
open scoped Interval
open Set MeasureTheory
open scoped Interval
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Set Filter
open scoped Topology ContDiff
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Neck Cometric ReturningCoefficients PassageDynamics Matrix

theorem OAI.ThreeManifold.ReturningPassage.returning_dynamics {right : Bool} {δ L : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (hL : 0 < L)
    (hconc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-force right δ p (t s) / 2) s)
    (h0 : t 0 = 0) (h1 : t L = 0)
    (hrange : ∀ s ∈ Ioo 0 L, t s ∈ Ioo 0 1)
    (henergy : ∀ s ∈ Icc 0 L, potential right δ p (t s) + v s ^ 2 = 1) :
    let T := t (L / 2)
    0 < v 0 ∧ v (L / 2) = 0 ∧ T ∈ Ioo 0 1 ∧
    MapsTo t (Icc 0 L) (Icc 0 T) ∧
    (∀ s ∈ Icc 0 L, t (L - s) = t s ∧ v (L - s) = -v s) ∧
    (∀ u ∈ Icc 0 T, 0 < force right δ p u) ∧
    ConvexOn ℝ (Icc 0 (L / 2)) v ∧
    ConcaveOn ℝ (Icc 0 (L / 2)) t ∧
      (∫ s in (0 : ℝ)..L, v s ^ 2) ≤ L * v 0 ^ 2 / 3 := by sorry
