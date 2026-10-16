-- Prove2me | Theorems.Thm_OAI_ThreeManifold_ReturningPassage_momentumVelocity_hasDerivAt
-- name    : OAI.ThreeManifold.ReturningPassage.momentumVelocity_hasDerivAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:41:36.409134+00:00
-- url     : https://prove2.me/theorems/54c27f84-fdd0-4d61-ac85-57ee24880338
-- title:
--   The momentum velocity $(v, R(t)p)$ satisfies the geodesic equation of the neck metric
-- statement:
--   Fix $\delta \in \mathbb{R}$. Let $a(x) = e^{-1/(2/3 - x)}$ for $x < 2/3$ and $a(x) = 0$ for $x \ge 2/3$ (so $a(0) = e^{-3/2}$), let $\mathcal{A}(x) = \int_0^x a(y)\,dy$, and let $\chi(x) = \rho\big(6(x - 5/12)\big)$, where $\rho$ is the standard smooth transition function ($\rho = 0$ on $(-\infty, 0]$, $\rho = 1$ on $[1, \infty)$). With $d_1(\tau) = 1 + \delta\mathcal{A}(\tau)$, $d_2(\tau) = 1 + \delta\mathcal{A}(1-\tau)$ and $\sigma(\tau) = \delta^2\chi(\tau)$ put
--   $$
--   P_\delta(\tau) = \begin{pmatrix} d_1(\tau) + d_2(\tau)\sigma(\tau)^2 & d_2(\tau)\sigma(\tau) \\ d_2(\tau)\sigma(\tau) & d_2(\tau) \end{pmatrix}, \qquad C_\delta = \begin{pmatrix} 0 & 1 \\ 1 & -\delta^2 \end{pmatrix}.
--   $$
--   For a flag $\mathrm{right} \in \{\mathrm{false}, \mathrm{true}\}$ the coordinate cometric is $R(\tau) = P_\delta(\tau)$ if the flag is false and $R(\tau) = C_\delta\, P_\delta(1-\tau)\, C_\delta^{\mathsf T}$ if it is true. It is a smooth family of symmetric $2\times 2$ matrices; $Q(\tau) = R(\tau)^{-1}$ is the corresponding metric matrix, and $R', R'', Q', Q''$ denote derivatives in $\tau$. For a momentum vector $p \in \mathbb{R}^2$ the force is $F(\tau) = \langle p, p\rangle_{R'(\tau)}$, its derivative is $G(\tau) = \langle p, p\rangle_{R''(\tau)}$, and the potential is $\Phi(\tau) = \langle p, p\rangle_{R(\tau)}$. Given functions $t, v : \mathbb{R} \to \mathbb{R}$, the momentum velocity is $T(s) = \big(v(s),\, R(t(s))\,p\big) \in \mathbb{R}\times\mathbb{R}^2$.
--
--   Points of $\mathbb{R}\times\mathbb{R}^2$ are written $X = (X_1, X_2)$, and $\langle x, y\rangle_A = x^{\mathsf T} A y$ for a $2\times 2$ matrix $A$. For matrices $P, A$ the connection term is $\Gamma_{P,A}(X, Y) = \big(-\tfrac12 \langle X_2, Y_2\rangle_A,\ \tfrac12 (X_1\, P A Y_2 + Y_1\, P A X_2)\big)$; for $P = Q^{-1}$ and $A = Q'$ this is the Christoffel contraction of the metric $d\tau^2 + Q(\tau)_{ij}\,dy^i dy^j$, whose coefficients depend only on the first coordinate $\tau$.
--
--   **Theorem.** Let $\mathrm{right}$ be a flag, $\delta, s \in \mathbb{R}$, $p \in \mathbb{R}^2$ and $t, v : \mathbb{R} \to \mathbb{R}$. Assume $\det R(t(s)) \neq 0$, that $t$ is differentiable at $s$ with $t'(s) = v(s)$, and that $v$ is differentiable at $s$ with $v'(s) = -F(t(s))/2$. Then the momentum velocity $T$ is differentiable at $s$ and
--   $$
--   T'(s) = -\,\Gamma_{R(t(s)),\, Q'(t(s))}\big(T(s), T(s)\big).
--   $$
--
--   In words: for the metric $d\tau^2 + Q(\tau)\,dy^2$ on the neck, whose coefficients do not depend on $y$, the momentum $p$ conjugate to $y$ is conserved, the $y$-velocity is $R(t)\,p$, and the height $t$ obeys the Newton equation $t'' = -F(t)/2$. The theorem says that a curve with these data has velocity $T$ satisfying the geodesic equation $T' = -\Gamma(T, T)$; this is how one-dimensional dynamics of the height is turned into genuine geodesics of the neck.
--
--   **Formalization Note** $Q(\tau)$ is `metricInverse right δ τ`, the Lean matrix inverse of `coordinateCometric right δ τ`, and $Q'$ is `deriv (metricInverse right δ)`. The hypotheses are needed only at the single parameter $s$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Returning.lean#L1969-L1993

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
open Neck Cometric Turning Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem OAI.ThreeManifold.ReturningPassage.momentumVelocity_hasDerivAt {right : Bool} {δ s : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (hdet : (coordinateCometric right δ (t s)).det ≠ 0)
    (ht : HasDerivAt t (v s) s) (hv : HasDerivAt v (-force right δ p (t s) / 2) s) :
    HasDerivAt (momentumVelocity right δ p t v)
      (-gamma (coordinateCometric right δ (t s)) (deriv (metricInverse right δ) (t s))
        (momentumVelocity right δ p t v s) (momentumVelocity right δ p t v s)) s := by sorry
