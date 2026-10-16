-- Prove2me | Theorems.Thm_OAI_ThreeManifold_ReturningPassage_returning_normal_identity
-- name    : OAI.ThreeManifold.ReturningPassage.returning_normal_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:42:10.154633+00:00
-- url     : https://prove2.me/theorems/7a468719-d8cf-4b7d-9859-eeb99371bf0e
-- title:
--   Normal index identity for a returning neck geodesic with momentum $p$
-- statement:
--   Fix $\delta \in \mathbb{R}$. Let $a(x) = e^{-1/(2/3 - x)}$ for $x < 2/3$ and $a(x) = 0$ for $x \ge 2/3$ (so $a(0) = e^{-3/2}$), let $\mathcal{A}(x) = \int_0^x a(y)\,dy$, and let $\chi(x) = \rho\big(6(x - 5/12)\big)$, where $\rho$ is the standard smooth transition function ($\rho = 0$ on $(-\infty, 0]$, $\rho = 1$ on $[1, \infty)$). With $d_1(\tau) = 1 + \delta\mathcal{A}(\tau)$, $d_2(\tau) = 1 + \delta\mathcal{A}(1-\tau)$ and $\sigma(\tau) = \delta^2\chi(\tau)$ put
--   $$
--   P_\delta(\tau) = \begin{pmatrix} d_1(\tau) + d_2(\tau)\sigma(\tau)^2 & d_2(\tau)\sigma(\tau) \\ d_2(\tau)\sigma(\tau) & d_2(\tau) \end{pmatrix}, \qquad C_\delta = \begin{pmatrix} 0 & 1 \\ 1 & -\delta^2 \end{pmatrix}.
--   $$
--   For a flag $\mathrm{right} \in \{\mathrm{false}, \mathrm{true}\}$ the coordinate cometric is $R(\tau) = P_\delta(\tau)$ if the flag is false and $R(\tau) = C_\delta\, P_\delta(1-\tau)\, C_\delta^{\mathsf T}$ if it is true. It is a smooth family of symmetric $2\times 2$ matrices; $Q(\tau) = R(\tau)^{-1}$ is the corresponding metric matrix, and $R', R'', Q', Q''$ denote derivatives in $\tau$. For a momentum vector $p \in \mathbb{R}^2$ the force is $F(\tau) = \langle p, p\rangle_{R'(\tau)}$, its derivative is $G(\tau) = \langle p, p\rangle_{R''(\tau)}$, and the potential is $\Phi(\tau) = \langle p, p\rangle_{R(\tau)}$. Given functions $t, v : \mathbb{R} \to \mathbb{R}$, the momentum velocity is $T(s) = \big(v(s),\, R(t(s))\,p\big) \in \mathbb{R}\times\mathbb{R}^2$.
--
--   Points of $\mathbb{R}\times\mathbb{R}^2$ are written $X = (X_1, X_2)$ with $X_1 \in \mathbb{R}$ and $X_2 \in \mathbb{R}^2$; for a real $2\times 2$ matrix $A$ and $x, y \in \mathbb{R}^2$ put $\langle x, y\rangle_A = x^{\mathsf T} A y$. For real $2\times 2$ matrices $P, Q, A, B$ define, for $X, Y, Z, T, V, D \in \mathbb{R}\times\mathbb{R}^2$:
--
--   - the metric $g_Q(X, Y) = X_1 Y_1 + \langle X_2, Y_2\rangle_Q$;
--   - the connection term $\Gamma(X, Y) = \big(-\tfrac12 \langle X_2, Y_2\rangle_A,\ \tfrac12 (X_1\, P A Y_2 + Y_1\, P A X_2)\big)$;
--   - its derivative $\Gamma'(X, Y) = \big(-\tfrac12 \langle X_2, Y_2\rangle_B,\ \tfrac12 (X_1\, S Y_2 + Y_1\, S X_2)\big)$ with $S = PB - PAPA$;
--   - the curvature term $\mathcal{R}(X, Y)Z = X_1\, \Gamma'(Y, Z) - Y_1\, \Gamma'(X, Z) + \Gamma(X, \Gamma(Y, Z)) - \Gamma(Y, \Gamma(X, Z))$;
--   - the normal index density $N(T, V, D) = g_Q\big(D + \Gamma(T, V), D + \Gamma(T, V)\big) - g_Q\big(V, \mathcal{R}(V, T)T\big) - g_Q\big(D + \Gamma(T, V), T\big)^2$.
--
--   When $P = Q^{-1}$, $A = Q'$ and $B = Q''$ for a family $Q(\tau)$ of symmetric matrices, $\Gamma$ and $\mathcal{R}$ are the Christoffel contraction and the curvature tensor of the metric $d\tau^2 + Q(\tau)_{ij}\,dy^i dy^j$ on a region of $\mathbb{R}\times\mathbb{R}^2$ whose coefficients depend only on the first coordinate $\tau$, and $N$ is the index-form integrand of a field $V$ with derivative $D$ along a curve with velocity $T$, with the component along $T$ removed.
--
--   For a field $V$ and a candidate derivative $D$ along the curve, the returning normal density at $s$ is $N_{\mathrm{ret}}(s) = N\big(T(s), V(s), D(s)\big)$ computed with $P = R(t(s))$, $Q = Q(t(s))$, $A = Q'(t(s))$, $B = Q''(t(s))$.
--
--   **Theorem.** Let $\mathrm{right}$ be a flag, $\delta, L, m \in \mathbb{R}$ with $L > 0$, $p \in \mathbb{R}^2$, and $t, v : \mathbb{R} \to \mathbb{R}$ such that for all $s \in [0, L]$: $\det R(t(s)) \neq 0$, $t'(s) = v(s)$ and $v'(s) = -F(t(s))/2$; moreover $t(0) = t(L) = 0$ and $v(L) = -v(0)$. Let $z, \dot z : \mathbb{R} \to \mathbb{R}^2$ and $w, \dot w : \mathbb{R} \to \mathbb{R}$ with $\dot z, \dot w$ continuous on $[0, L]$, $z' = \dot z$ and $w' = \dot w$ at every point of $[0, L]$, and $w(0) = w(L) = 0$. Assume finally that for every $s \in [0, L]$ the function $r \mapsto g_{Q(t(r))}\big((w(r), z(r)), T(r)\big)$ has derivative $m$ at $s$. Then, with $V = (w, z)$, $D = (\dot w, \dot z)$, $\zeta(s) = \dot z(s) - w(s)\, R'(t(s))\,p$, and $z_1$ the first component of $z$,
--   $$
--   \int_0^L N_{\mathrm{ret}}(s)\,ds = \int_0^L \Big( \langle \zeta(s), \zeta(s)\rangle_{R(t(s))^{-1}} + \dot w(s)^2 - \tfrac12\, G(t(s))\, w(s)^2 \Big)\,ds + \frac{\delta\, a(0)\, v(0)}{2}\big(z_1(0)^2 + z_1(L)^2\big) - \frac{\big(p \cdot (z(L) - z(0))\big)^2}{L}.
--   $$
--
--   The curve $s \mapsto (t(s), y(s))$ described here is a neck geodesic that starts and ends on the boundary level $\tau = 0$ (a returning passage). The identity expresses the normal index form of a variation field vanishing in the height direction at both ends as an energy integral with an explicit potential term $-\tfrac12 G w^2$, a boundary contribution coming from the shape of the metric at $\tau = 0$, and a negative term measuring the net horizontal displacement of the field along $p$. It is the starting point for proving that such passages carry nonnegative index forms.
--
--   **Formalization Note** The densities are `returnNormalDensity` and `energyDensity`; $F$ and $G$ are `force` and `forceDerivative`, and $R(t(s))^{-1}$ is the Lean matrix inverse, which is a genuine inverse because the determinant is assumed nonzero. $Q'$ and $Q''$ are iterated `deriv`s of `metricInverse right δ`; the term $z_1$ is `z · 0` and $a(0)$ is `Cometric.a 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Returning.lean#L2027-L2149

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
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem OAI.ThreeManifold.ReturningPassage.returning_normal_identity {right : Bool} {δ L m : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (hL : 0 < L)
    (hdet : ∀ s ∈ Icc 0 L, (coordinateCometric right δ (t s)).det ≠ 0)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-force right δ p (t s) / 2) s)
    (h0 : t 0 = 0) (h1 : t L = 0) (hvL : v L = -v 0)
    {z z' : ℝ → TVec} {w w' : ℝ → ℝ}
    (hzc : ContinuousOn z' (Icc 0 L)) (hwc : ContinuousOn w' (Icc 0 L))
    (hz : ∀ s ∈ Icc 0 L, HasDerivAt z (z' s) s)
    (hw : ∀ s ∈ Icc 0 L, HasDerivAt w (w' s) s)
    (hwa : w 0 = 0) (hwb : w L = 0)
    (hlin : ∀ s ∈ Icc 0 L, HasDerivAt
      (fun r => metric (metricInverse right δ (t r)) (w r, z r)
        (momentumVelocity right δ p t v r)) m s) :
    (∫ s in (0 : ℝ)..L, returnNormalDensity right δ p t v
      (fun r => (w r, z r)) (fun r => (w' r, z' r)) s) =
    (∫ s in (0 : ℝ)..L,
      energyDensity (fun s => (coordinateCometric right δ (t s))⁻¹)
        (fun s => deriv (coordinateCometric right δ) (t s) *ᵥ p)
        (fun s => -forceDerivative right δ p (t s) / 2) z' w w' s) +
      δ * a 0 * v 0 / 2 * ((z 0 0) ^ 2 + (z L 0) ^ 2) -
        (p ⬝ᵥ (z L - z 0)) ^ 2 / L := by sorry
