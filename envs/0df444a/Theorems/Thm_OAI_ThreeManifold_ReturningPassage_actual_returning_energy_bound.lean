-- Prove2me | Theorems.Thm_OAI_ThreeManifold_ReturningPassage_actual_returning_energy_bound
-- name    : OAI.ThreeManifold.ReturningPassage.actual_returning_energy_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:33:37.374063+00:00
-- url     : https://prove2.me/theorems/2c46dc9f-2d86-475e-b3a4-f1589108829a
-- title:
--   Lower bound for the quadratic energy along a returning neck passage
-- statement:
--   Let $a(u) = e^{-1/(2/3-u)}$ for $u < 2/3$ and $a(u) = 0$ for $u \ge 2/3$ (a smooth cutoff), let $A(u) = \int_0^u a(y)\,dy$, and let $\chi(t) = \sigma\big(6(t - 5/12)\big)$ be a smooth step, where $\sigma(x) = \psi(x)/(\psi(x) + \psi(1-x))$ and $\psi(x) = e^{-1/x}$ for $x > 0$, $\psi(x) = 0$ for $x \le 0$. For a real parameter $\delta$ put $d_1(t) = 1 + \delta A(t)$, $d_2(t) = 1 + \delta A(1-t)$, $\eta(t) = \delta^2 \chi(t)$ and
--   $$
--   P_\delta(t) = \begin{pmatrix} d_1(t) + d_2(t)\,\eta(t)^2 & d_2(t)\,\eta(t) \\ d_2(t)\,\eta(t) & d_2(t) \end{pmatrix}, \qquad \widetilde P_\delta(t) = C_\delta\, P_\delta(1-t)\, C_\delta^{\top}, \qquad C_\delta = \begin{pmatrix} 0 & 1 \\ 1 & -\delta^2 \end{pmatrix}.
--   $$
--   The *coordinate cometric* $R_\delta = R^{\rho}_\delta : \mathbb{R} \to \mathbb{R}^{2 \times 2}$ with end flag $\rho \in \{\text{left}, \text{right}\}$ is $R^{\text{left}}_\delta = P_\delta$ and $R^{\text{right}}_\delta = \widetilde P_\delta$; it is a smooth family of symmetric matrices, and $R_\delta'$, $R_\delta''$ denote its first and second derivatives in $t$.
--
--   For a $2 \times 2$ matrix $Q$ and $u, v \in \mathbb{R}^2$ write $\langle u, v\rangle_Q = u^{\top} Q v$, write $|q|^2 = q_1^2 + q_2^2$ for $q = (q_1, q_2)$, and let $e = (1, 0)$. Let $a_0 = e^{-3/2}$ (which equals $a(0)$), $\beta = \tfrac12\big(1 + e^{-9/26}\big)$, and for $C > 0$ let
--   $$
--   C_{\mathrm m}(C) = a(0) + \sqrt{2C\,a(0)} + 2\sqrt{2C\,a(0)/3}.
--   $$
--   Say that $\delta$ is *small for* $(C_e, C_m)$ if $0 < \delta \le 1$, $\delta \le 1/(2C_m)$ and $\delta \le (1-\beta)/(2C_m + C_e a_0)$.
--
--   Fix an end flag $\rho$, $\delta$, $C$, $L \in \mathbb{R}$ and $p = (p_1,p_2) \in \mathbb{R}^2$; write $R = R^\rho_\delta$, $V(u) = p^{\top}R(u)p$ and $F(u) = p^{\top}R'(u)p$.
--
--   **Theorem.** Assume:
--   - $C \ge 18$ and $\delta$ is small for $(3C, C_{\mathrm m}(C))$;
--   - for all $u \in [0,1]$ and $q \in \mathbb{R}^2$: $|q|^2/9 \le q^{\top}R(u)q \le 18|q|^2$, $|R'(u)e|^2 \le C^2\delta^2$, $q^{\top}(-R''(u))q \ge 0$, and $|R'(u)p|^2 \le C\delta\, p^{\top}(-R''(u))p$;
--   - $L > 0$, and $t, v : \mathbb{R} \to \mathbb{R}$ satisfy $t' = v$, $v' = -\tfrac12 F(t)$ at every point of $[0,L]$, $t(0) = t(L) = 0$, $t(s) \in (0,1)$ for $s \in (0,L)$, $V(t(s)) + v(s)^2 = 1$ for $s \in [0,L]$, and $t(L/2) > 1/4$;
--   - $z, z' : \mathbb{R} \to \mathbb{R}^2$ and $w, w' : \mathbb{R} \to \mathbb{R}$ with $z'$ and $w'$ continuous on $[0,L]$, $z'(s)$ the derivative of $z$ and $w'(s)$ the derivative of $w$ at every $s \in [0,L]$, and $w(0) = w(L) = 0$.
--
--   Define along the passage $Q(s) = R(t(s))^{-1}$, $k(s) = R'(t(s))\,p$, $h(s) = -\tfrac12\, p^{\top}R''(t(s))\,p$, and the energy density
--   $$
--   \mathcal E(s) = \big(z'(s) - w(s)k(s)\big)^{\top} Q(s) \big(z'(s) - w(s)k(s)\big) + w'(s)^2 + h(s)\,w(s)^2 .
--   $$
--   Then, with $\Delta z = z(L) - z(0)$,
--   $$
--   \int_0^L \mathcal E(s)\, ds + \frac{\delta\, a_0\, v(0)}{4}\,\big(e \cdot \Delta z\big)^2 - \frac{(p \cdot \Delta z)^2}{L} \ge 0 .
--   $$
--
--   The inequality is a lower bound for a quadratic energy of variations $(z, w)$ along a returning passage of depth more than $1/4$: up to a small boundary correction in the $e$-direction, the energy dominates $(p\cdot\Delta z)^2/L$. Bounds of this kind feed into the index estimates for returning neck geodesics. The curvature-type hypotheses on $R$ are exactly the uniform bounds provided for all sufficiently small $\delta$ by the companion result on uniform turning parameters.
--
--   **Formalization Note** `coordinateCometric right δ` is $R^{\rho}_\delta$ (`right = false` gives $P_\delta$ = `Cometric.P δ`, `right = true` gives `PEnd δ`); `pairing Q u v` $= u^{\top}Qv$, `qform Q q` $= q^{\top}Qq$, `sqnorm q` $= q_1^2+q_2^2$; Lean indexes the coordinates of $p$ as `p 0`, `p 1`, so $p_1$ is `p 0`. Derivatives are Lean's `deriv`, which are genuine derivatives here because $R_\delta$ is smooth. The smallness condition is `SmallParameter (3 * C) (sourceMixed C) δ`, $C_{\mathrm m}$ is `sourceMixed`, $a_0$ is `Turning.aZero` and $\beta$ is `Turning.beta`; $\mathcal E$ is `energyDensity` and $e\cdot\Delta z$ is a dot product. The matrix inverse is Lean's total inverse, which is the genuine inverse here because the lower bound $q^{\top}R(u)q \ge |q|^2/9$ makes $R(t(s))$ positive definite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Returning.lean#L1421-L1556

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
open Neck Cometric ReturningCoefficients PassageDynamics Matrix DirectTurning Turning

theorem OAI.ThreeManifold.ReturningPassage.actual_returning_energy_bound {right : Bool} {δ C L : ℝ} {p : TVec}
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
    (h0 : t 0 = 0) (h1 : t L = 0)
    (hrange : ∀ s ∈ Ioo 0 L, t s ∈ Ioo 0 1)
    (henergy : ∀ s ∈ Icc 0 L, potential right δ p (t s) + v s ^ 2 = 1)
    {z z' : ℝ → TVec} {w w' : ℝ → ℝ}
    (hzc : ContinuousOn z' (Icc 0 L)) (hw'c : ContinuousOn w' (Icc 0 L))
    (hz : ∀ s ∈ Icc 0 L, HasDerivAt z (z' s) s)
    (hw : ∀ s ∈ Icc 0 L, HasDerivAt w (w' s) s)
    (hwa : w 0 = 0) (hwb : w L = 0) :
    0 ≤ (∫ s in (0 : ℝ)..L,
      energyDensity (fun s => (coordinateCometric right δ (t s))⁻¹)
        (fun s => deriv (coordinateCometric right δ) (t s) *ᵥ p)
        (fun s => -forceDerivative right δ p (t s) / 2) z' w w' s) +
      (δ * aZero * v 0 / 4) * (e ⬝ᵥ (z L - z 0)) ^ 2 - (p ⬝ᵥ (z L - z 0)) ^ 2 / L := by sorry
