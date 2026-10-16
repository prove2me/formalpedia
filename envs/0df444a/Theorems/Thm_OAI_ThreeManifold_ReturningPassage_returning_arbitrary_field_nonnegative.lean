-- Prove2me | Theorems.Thm_OAI_ThreeManifold_ReturningPassage_returning_arbitrary_field_nonnegative
-- name    : OAI.ThreeManifold.ReturningPassage.returning_arbitrary_field_nonnegative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:42:37.440926+00:00
-- url     : https://prove2.me/theorems/05cac5e7-981c-4de1-8063-f02f605bfc1d
-- title:
--   Returning neck passages have nonnegative normal index form for every smooth variation field
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
--   For a field $V : \mathbb{R} \to \mathbb{R}\times\mathbb{R}^2$ the returning normal density is $N_{\mathrm{ret}}[V](s) = N\big(T(s), V(s), V'(s)\big)$ computed with $P = R(t(s))$, $Q = Q(t(s))$, $A = Q'(t(s))$, $B = Q''(t(s))$. Write $|q|^2 = q_1^2 + q_2^2$ and $e_1 = (1, 0)$. Let $a_0 = e^{-3/2}$ and $\beta_0 = \tfrac12(1 + e^{-9/26})$, and for $C \in \mathbb{R}$ let $C_m = a(0) + \sqrt{2Ca(0)} + 2\sqrt{2Ca(0)/3}$.
--
--   **Theorem.** Let $\mathrm{right}$ be a flag, $\delta, C, L \in \mathbb{R}$, $p \in \mathbb{R}^2$ and $t, v : \mathbb{R} \to \mathbb{R}$. Assume:
--
--   1. $C \ge 18$, and $\delta$ is small: $0 < \delta \le 1$, $\delta \le 1/(2C_m)$ and $\delta \le (1 - \beta_0)/(2C_m + 3C a_0)$;
--   2. for all $\tau \in [0,1]$ and $q \in \mathbb{R}^2$: $|q|^2/9 \le \langle q, q\rangle_{R(\tau)} \le 18\,|q|^2$, $\ |R'(\tau) e_1|^2 \le C^2\delta^2$, $\ \langle q, q\rangle_{-R''(\tau)} \ge 0$, and $|R'(\tau)p|^2 \le C\delta\,\langle p, p\rangle_{-R''(\tau)}$;
--   3. $L > 0$ and $t(L/2) > 1/4$;
--   4. for all $s \in [0, L]$: $t'(s) = v(s)$, $v'(s) = -F(t(s))/2$, $t$ and $v$ are $C^\infty$ at $s$, and $\Phi(t(s)) + v(s)^2 = 1$;
--   5. $t(0) = t(L) = 0$ and $t(s) \in (0, 1)$ for all $s \in (0, L)$;
--   6. $V : \mathbb{R} \to \mathbb{R}\times\mathbb{R}^2$ is $C^\infty$ at every point of $[0, L]$.
--
--   Then
--   $$
--   \int_0^L N_{\mathrm{ret}}[V](s)\,ds \ \ge\ 0 .
--   $$
--
--   Hypotheses 4 and 5 describe a unit-speed geodesic of the neck metric $d\tau^2 + Q(\tau)\,dy^2$ with conserved momentum $p$ that enters the neck at the level $\tau = 0$, rises above $\tau = 1/4$, and returns to $\tau = 0$ (a returning passage); hypotheses 1 and 2 are the quantitative properties of the cometric for small $\delta$. The conclusion says the index form of such a passage, restricted to the part of a variation field normal to the geodesic, is nonnegative for every smooth field, with no boundary conditions on $V$. This is the local index estimate used to rule out conjugate points along geodesic segments that dip into the neck and come back.
--
--   **Formalization Note** The smallness condition is `SmallParameter (3 * C) (sourceMixed C) δ`, $|q|^2$ is `sqnorm`, $\langle q, q\rangle_M$ is `qform M q`, and $V'$ is `deriv V`. $Q(\tau)$ is the Lean matrix inverse of `coordinateCometric right δ τ`; the hypotheses force $\det R(t(s)) > 0$ on $[0, L]$, so it is a genuine inverse there.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Returning.lean#L2265-L2328

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
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem OAI.ThreeManifold.ReturningPassage.returning_arbitrary_field_nonnegative {right : Bool} {δ C L : ℝ} {p : TVec}
    {t v : ℝ → ℝ} (hC : 18 ≤ C)
    (hδ : SmallParameter (3 * C) (sourceMixed C) δ)
    (hbound : ∀ u ∈ Icc 0 1, ∀ q,
      sqnorm q / 9 ≤ qform (coordinateCometric right δ u) q ∧
      qform (coordinateCometric right δ u) q ≤ 18 * sqnorm q)
    (hder : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ e) ≤ C ^ 2 * δ ^ 2)
    (hconc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (hdom : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ p) ≤
      C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) p)
    (hL : 0 < L) (hstar : 1 / 4 < t (L / 2))
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-force right δ p (t s) / 2) s)
    (hta : ∀ s ∈ Icc 0 L, ContDiffAt ℝ ∞ t s)
    (hva : ∀ s ∈ Icc 0 L, ContDiffAt ℝ ∞ v s)
    (h0 : t 0 = 0) (h1 : t L = 0)
    (hrange : ∀ s ∈ Ioo 0 L, t s ∈ Ioo 0 1)
    (henergy : ∀ s ∈ Icc 0 L, potential right δ p (t s) + v s ^ 2 = 1)
    {V : ℝ → Vec} (hV : ∀ s ∈ Icc 0 L, ContDiffAt ℝ ∞ V s) :
    0 ≤ (∫ s in (0 : ℝ)..L, returnNormalDensity right δ p t v V (deriv V) s) := by sorry
