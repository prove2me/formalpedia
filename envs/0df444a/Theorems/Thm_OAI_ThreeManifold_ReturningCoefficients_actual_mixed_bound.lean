-- Prove2me | Theorems.Thm_OAI_ThreeManifold_ReturningCoefficients_actual_mixed_bound
-- name    : OAI.ThreeManifold.ReturningCoefficients.actual_mixed_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:31:43.035397+00:00
-- url     : https://prove2.me/theorems/d131ca34-68d2-4fbe-89d3-297a5d8780ee
-- title:
--   Mixed-coefficient bound $|e^{\top}R_\delta(t)p - p_1| \le (a(0)+\sqrt{2Ca(0)})\,\delta\,|p_1|$ along a passage
-- statement:
--   Let $a(u) = e^{-1/(2/3-u)}$ for $u < 2/3$ and $a(u) = 0$ for $u \ge 2/3$ (a smooth cutoff), let $A(u) = \int_0^u a(y)\,dy$, and let $\chi(t) = \sigma\big(6(t - 5/12)\big)$ be a smooth step, where $\sigma(x) = \psi(x)/(\psi(x) + \psi(1-x))$ and $\psi(x) = e^{-1/x}$ for $x > 0$, $\psi(x) = 0$ for $x \le 0$. For a real parameter $\delta$ put $d_1(t) = 1 + \delta A(t)$, $d_2(t) = 1 + \delta A(1-t)$, $\eta(t) = \delta^2 \chi(t)$ and
--   $$
--   P_\delta(t) = \begin{pmatrix} d_1(t) + d_2(t)\,\eta(t)^2 & d_2(t)\,\eta(t) \\ d_2(t)\,\eta(t) & d_2(t) \end{pmatrix}, \qquad \widetilde P_\delta(t) = C_\delta\, P_\delta(1-t)\, C_\delta^{\top}, \qquad C_\delta = \begin{pmatrix} 0 & 1 \\ 1 & -\delta^2 \end{pmatrix}.
--   $$
--   The *coordinate cometric* $R_\delta = R^{\rho}_\delta : \mathbb{R} \to \mathbb{R}^{2 \times 2}$ with end flag $\rho \in \{\text{left}, \text{right}\}$ is $R^{\text{left}}_\delta = P_\delta$ and $R^{\text{right}}_\delta = \widetilde P_\delta$; it is a smooth family of symmetric matrices, and $R_\delta'$, $R_\delta''$ denote its first and second derivatives in $t$.
--
--   For a $2 \times 2$ matrix $Q$ and $u, v \in \mathbb{R}^2$ write $\langle u, v\rangle_Q = u^{\top} Q v$, write $|q|^2 = q_1^2 + q_2^2$ for $q = (q_1, q_2)$, and let $e = (1, 0)$.
--
--   **Theorem.** Fix an end flag $\rho$, real numbers $\delta, T, C$ and a vector $p = (p_1, p_2) \in \mathbb{R}^2$, and write $R = R^\rho_\delta$. Assume
--   - $\delta \ge 0$, $C > 0$ and $0 \le T \le 1$;
--   - (concavity) $q^{\top}\big(-R''(t)\big)q \ge 0$ for all $t \in [0,1]$ and $q \in \mathbb{R}^2$;
--   - (derivative bound in direction $e$) $|R'(t)e|^2 \le C^2\delta^2$ for all $t \in [0,1]$;
--   - (nonnegative force) $p^{\top} R'(t) p \ge 0$ for all $t \in [0,T]$.
--
--   Then for every $t \in [0,T]$,
--   $$
--   \big|\langle e, p\rangle_{R(t)} - p_1\big| \le \big(a(0) + \sqrt{2C\,a(0)}\big)\,\delta\,|p_1| .
--   $$
--
--   Since $\langle e, p\rangle_{R(0)} = p_1$, the theorem says that the mixed coefficient $e^{\top}R(t)p$ moves away from its initial value by at most $O(\delta)\,|p_1|$ as long as the force $p^{\top}R'p$ stays nonnegative. Integrated along a returning passage, this controls the mixed coefficient in the quadratic estimates for the index of returning neck geodesics.
--
--   **Formalization Note** `coordinateCometric right δ` is $R^{\rho}_\delta$ (`right = false` gives $P_\delta$ = `Cometric.P δ`, `right = true` gives `PEnd δ`); `pairing Q u v` $= u^{\top}Qv$, `qform Q q` $= q^{\top}Qq$, `sqnorm q` $= q_1^2+q_2^2$; Lean indexes the coordinates of $p$ as `p 0`, `p 1`, so $p_1$ is `p 0`. Derivatives are Lean's `deriv`, which are genuine derivatives here because $R_\delta$ is smooth.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Returning.lean#L908-L963

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning

open OAI OAI.ThreeManifold OAI.ThreeManifold.ReturningCoefficients
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
open Neck Cometric Matrix

theorem OAI.ThreeManifold.ReturningCoefficients.actual_mixed_bound {right : Bool} {δ T C : ℝ} {p : TVec}
    (hδ : 0 ≤ δ) (hC : 0 < C) (hT : T ∈ Icc 0 1)
    (hconc : ∀ t ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) t) q)
    (hder : ∀ t ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) t *ᵥ e) ≤ C ^ 2 * δ ^ 2)
    (hforce : ∀ t ∈ Icc 0 T, 0 ≤ pairing (deriv (coordinateCometric right δ) t) p p) :
    ∀ t ∈ Icc 0 T,
      |pairing (coordinateCometric right δ t) e p - p 0| ≤
        (a 0 + Real.sqrt (2 * C * a 0)) * δ * |p 0| := by sorry
