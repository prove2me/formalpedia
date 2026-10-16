-- Prove2me | Theorems.Thm_OAI_ThreeManifold_Neck_normal_index_integral
-- name    : OAI.ThreeManifold.Neck.normal_index_integral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:37:05.776559+00:00
-- url     : https://prove2.me/theorems/ca827b43-5da1-4e5a-b847-62a9fc202669
-- title:
--   Integrated normal index density along a geodesic of $d\tau^2 + Q(\tau)\,dy^2$: energy, boundary term and tangential correction
-- statement:
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
--   In addition define the coordinate energy density and the boundary term
--   $$
--   E(T, V, D) = D_1^2 + \langle D_2, D_2\rangle_Q + 2V_1 \langle D_2, T_2\rangle_A + \tfrac12 V_1^2 \langle T_2, T_2\rangle_B, \qquad \beta_A(T, V) = -\tfrac12 T_1 \langle V_2, V_2\rangle_A + V_1 \langle T_2, V_2\rangle_A.
--   $$
--
--   **Theorem.** Let $a, c, m \in \mathbb{R}$ and $I = [\min(a,c), \max(a,c)]$. Let $P, Q, A, B : \mathbb{R} \to \mathbb{R}^{2\times 2}$, $t, v, w, \dot w : \mathbb{R} \to \mathbb{R}$ and $u, z, \dot z : \mathbb{R} \to \mathbb{R}^2$. Abbreviate $P_s = P(t(s))$, and similarly $Q_s, A_s, B_s$. Assume:
--
--   1. $s \mapsto P_s, Q_s, A_s, B_s$ and $v, u, w, z, \dot w, \dot z$ are continuous on $I$;
--   2. for all $s \in I$: $Q_s P_s = 1$ and $P_s, Q_s, A_s, B_s$ are symmetric;
--   3. for all $s \in I$: $t'(s) = v(s)$, $v'(s) = \tfrac12 \langle u(s), u(s)\rangle_{A_s}$ and $u'(s) = -v(s)\, P_s A_s\, u(s)$;
--   4. for all $s \in I$: $Q$ is differentiable at $t(s)$ with $Q'(t(s)) = A_s$, and $A$ is differentiable at $t(s)$ with $A'(t(s)) = B_s$;
--   5. for all $s \in I$: $w'(s) = \dot w(s)$ and $z'(s) = \dot z(s)$;
--   6. for all $s \in I$ the function $r \mapsto g_{Q_r}\big((w(r), z(r)), (v(r), u(r))\big)$ has derivative $m$ at $s$.
--
--   Write $T(s) = (v(s), u(s))$, $V(s) = (w(s), z(s))$, $D(s) = (\dot w(s), \dot z(s))$, let $N(s)$ and $E(s)$ be $N$ and $E$ evaluated at $(T(s), V(s), D(s))$ with the matrices $P_s, Q_s, A_s, B_s$, and let $\beta(s) = \beta_{A_s}(T(s), V(s))$. Then
--   $$
--   \int_a^c N(s)\,ds = \int_a^c E(s)\,ds - \big(\beta(c) - \beta(a)\big) - (c - a)\,m^2 .
--   $$
--
--   Hypothesis 3 says that $T = (v, u)$ solves the geodesic equation $T' = -\Gamma(T, T)$ while $t' = T_1$, i.e. $T$ is the velocity of a geodesic of $d\tau^2 + Q(\tau)\,dy^2$ in these coordinates; hypothesis 6 says that the tangential component $g_Q(V, T)$ of the variation field grows linearly. The identity rewrites the normal index form as a manifestly computable energy integral, a boundary contribution and the explicit correction $(c-a)m^2$; it is the basis for the sign estimates on index forms of geodesics crossing the neck.
--
--   **Formalization Note** The integrals are oriented interval integrals $\int_a^c$, the hypotheses are imposed on `uIcc a c`, and all derivatives are two-sided (`HasDerivAt`), also at the endpoints of $I$. The densities are `normalDensity`, `coordinateEnergyDensity` and `boundaryTerm`; the curvature term is `curvatureJet`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Returning.lean#L1816-L1893

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning

open OAI OAI.ThreeManifold OAI.ThreeManifold.Neck
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
open Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem OAI.ThreeManifold.Neck.normal_index_integral
    {P Q A B : ℝ → TMat} {t v w : ℝ → ℝ} {u z : ℝ → TVec}
    {wd : ℝ → ℝ} {zd : ℝ → TVec} {a c m : ℝ}
    (hP : ContinuousOn (P ∘ t) (uIcc a c))
    (hQ : ContinuousOn (Q ∘ t) (uIcc a c))
    (hA : ContinuousOn (A ∘ t) (uIcc a c))
    (hB : ContinuousOn (B ∘ t) (uIcc a c))
    (hv : ContinuousOn v (uIcc a c)) (hu : ContinuousOn u (uIcc a c))
    (hw : ContinuousOn w (uIcc a c)) (hz : ContinuousOn z (uIcc a c))
    (hwd : ContinuousOn wd (uIcc a c)) (hzd : ContinuousOn zd (uIcc a c))
    (hQP : ∀ s ∈ uIcc a c, Q (t s) * P (t s) = 1)
    (hQs : ∀ s ∈ uIcc a c, (Q (t s))ᵀ = Q (t s))
    (hPs : ∀ s ∈ uIcc a c, (P (t s))ᵀ = P (t s))
    (hAs : ∀ s ∈ uIcc a c, (A (t s))ᵀ = A (t s))
    (hBs : ∀ s ∈ uIcc a c, (B (t s))ᵀ = B (t s))
    (ht : ∀ s ∈ uIcc a c, HasDerivAt t (v s) s)
    (hv' : ∀ s ∈ uIcc a c,
      HasDerivAt v ((1 / 2 : ℝ) * pairing (A (t s)) (u s) (u s)) s)
    (hu' : ∀ s ∈ uIcc a c,
      HasDerivAt u (-v s • (P (t s) *ᵥ (A (t s) *ᵥ u s))) s)
    (hQ' : ∀ s ∈ uIcc a c, HasDerivAt Q (A (t s)) (t s))
    (hA' : ∀ s ∈ uIcc a c, HasDerivAt A (B (t s)) (t s))
    (hw' : ∀ s ∈ uIcc a c, HasDerivAt w (wd s) s)
    (hz' : ∀ s ∈ uIcc a c, HasDerivAt z (zd s) s)
    (hlin : ∀ s ∈ uIcc a c,
      HasDerivAt (fun r => metric (Q (t r)) (w r, z r) (v r, u r)) m s) :
    (∫ s in a..c, normalDensity (P (t s)) (Q (t s)) (A (t s)) (B (t s))
      (v s, u s) (w s, z s) (wd s, zd s)) =
      (∫ s in a..c, coordinateEnergyDensity (Q (t s)) (A (t s)) (B (t s))
        (v s, u s) (w s, z s) (wd s, zd s)) -
      (boundaryTerm (A (t c)) (v c, u c) (w c, z c) -
        boundaryTerm (A (t a)) (v a, u a) (w a, z a)) - (c - a) * m ^ 2 := by sorry
