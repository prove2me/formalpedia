-- Prove2me | Theorems.Thm_OAI_ThreeManifold_ReturningPassage_uniform_turning_parameters
-- name    : OAI.ThreeManifold.ReturningPassage.uniform_turning_parameters
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:35:57.180806+00:00
-- url     : https://prove2.me/theorems/06aab315-839a-4d4f-99f5-baac5d94bb62
-- title:
--   Uniform bounds on the coordinate cometric for all small $\delta$
-- statement:
--   Let $a(u) = e^{-1/(2/3-u)}$ for $u < 2/3$ and $a(u) = 0$ for $u \ge 2/3$ (a smooth cutoff), let $A(u) = \int_0^u a(y)\,dy$, and let $\chi(t) = \sigma\big(6(t - 5/12)\big)$ be a smooth step, where $\sigma(x) = \psi(x)/(\psi(x) + \psi(1-x))$ and $\psi(x) = e^{-1/x}$ for $x > 0$, $\psi(x) = 0$ for $x \le 0$. For a real parameter $\delta$ put $d_1(t) = 1 + \delta A(t)$, $d_2(t) = 1 + \delta A(1-t)$, $\eta(t) = \delta^2 \chi(t)$ and
--   $$
--   P_\delta(t) = \begin{pmatrix} d_1(t) + d_2(t)\,\eta(t)^2 & d_2(t)\,\eta(t) \\ d_2(t)\,\eta(t) & d_2(t) \end{pmatrix}, \qquad \widetilde P_\delta(t) = C_\delta\, P_\delta(1-t)\, C_\delta^{\top}, \qquad C_\delta = \begin{pmatrix} 0 & 1 \\ 1 & -\delta^2 \end{pmatrix}.
--   $$
--   The *coordinate cometric* $R_\delta = R^{\rho}_\delta : \mathbb{R} \to \mathbb{R}^{2 \times 2}$ with end flag $\rho \in \{\text{left}, \text{right}\}$ is $R^{\text{left}}_\delta = P_\delta$ and $R^{\text{right}}_\delta = \widetilde P_\delta$; it is a smooth family of symmetric matrices, and $R_\delta'$, $R_\delta''$ denote its first and second derivatives in $t$.
--
--   Write $|q|^2 = q_1^2 + q_2^2$. Let $a_0 = e^{-3/2}$, $\beta = \tfrac12\big(1 + e^{-9/26}\big)$, and for $C \in \mathbb{R}$ let $C_{\mathrm m}(C) = a(0) + \sqrt{2C\,a(0)} + 2\sqrt{2C\,a(0)/3}$. Say that $\delta$ is *small for* $(C_e, C_m)$ if $0 < \delta \le 1$, $\delta \le 1/(2C_m)$ and $\delta \le (1-\beta)/(2C_m + C_e a_0)$.
--
--   **Theorem.** There exist real numbers $\delta_0$ and $C$ with $0 < \delta_0 \le 1/2$ and $C \ge 18$ such that for every $\delta \in (0, \delta_0]$: $\delta$ is small for $(3C, C_{\mathrm m}(C))$, and for both end flags $\rho$, every $u \in [0,1]$ and every $q \in \mathbb{R}^2$, writing $R = R^\rho_\delta$,
--   $$
--   \frac{|q|^2}{9} \le q^{\top}R(u)q \le 18|q|^2, \quad |R'(u)q|^2 \le C^2\delta^2|q|^2, \quad 0 \le q^{\top}\big(-R''(u)\big)q, \quad |R'(u)q|^2 \le C\delta\; q^{\top}\big(-R''(u)\big)q .
--   $$
--
--   These are exactly the uniform hypotheses (with one constant $C$ that also governs the smallness of $\delta$) needed by the energy estimates for returning passages through the neck: uniform ellipticity of the cometric, an $O(\delta)$ bound on its derivative, concavity in $u$, and domination of the first derivative by the second.
--
--   **Formalization Note** `coordinateCometric right δ` is $R^{\rho}_\delta$ (`right = false` gives $P_\delta$ = `Cometric.P δ`, `right = true` gives `PEnd δ`); `pairing Q u v` $= u^{\top}Qv$, `qform Q q` $= q^{\top}Qq$, `sqnorm q` $= q_1^2+q_2^2$; Lean indexes the coordinates of $p$ as `p 0`, `p 1`, so $p_1$ is `p 0`. Derivatives are Lean's `deriv`, which are genuine derivatives here because $R_\delta$ is smooth. The smallness condition is `SmallParameter (3 * C) (sourceMixed C) δ`, with `sourceMixed` $= C_{\mathrm m}$, `Turning.aZero` $= a_0$ and `Turning.beta` $= \beta$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Returning.lean#L1558-L1597

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

theorem OAI.ThreeManifold.ReturningPassage.uniform_turning_parameters : ∃ δ₀ C : ℝ,
    0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ 18 ≤ C ∧
    ∀ δ ∈ Ioc (0 : ℝ) δ₀,
      SmallParameter (3 * C) (sourceMixed C) δ ∧
      ∀ right : Bool, ∀ u ∈ Icc (0 : ℝ) 1, ∀ q : TVec,
        (sqnorm q / 9 ≤ qform (coordinateCometric right δ u) q ∧
          qform (coordinateCometric right δ u) q ≤ 18 * sqnorm q) ∧
        sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C ^ 2 * δ ^ 2 * sqnorm q ∧
        0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q ∧
        sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤
          C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) q := by sorry
