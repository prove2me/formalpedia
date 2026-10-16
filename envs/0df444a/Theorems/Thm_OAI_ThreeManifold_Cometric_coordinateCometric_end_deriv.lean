-- Prove2me | Theorems.Thm_OAI_ThreeManifold_Cometric_coordinateCometric_end_deriv
-- name    : OAI.ThreeManifold.Cometric.coordinateCometric_end_deriv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:31:14.826891+00:00
-- url     : https://prove2.me/theorems/92d270ac-d120-4be9-9c47-1f3a367638d4
-- title:
--   Derivative of the coordinate cometric near the end of the neck
-- statement:
--   Let $a(u) = e^{-1/(2/3-u)}$ for $u < 2/3$ and $a(u) = 0$ for $u \ge 2/3$ (a smooth cutoff), let $A(u) = \int_0^u a(y)\,dy$, and let $\chi(t) = \sigma\big(6(t - 5/12)\big)$ be a smooth step, where $\sigma(x) = \psi(x)/(\psi(x) + \psi(1-x))$ and $\psi(x) = e^{-1/x}$ for $x > 0$, $\psi(x) = 0$ for $x \le 0$. For a real parameter $\delta$ put $d_1(t) = 1 + \delta A(t)$, $d_2(t) = 1 + \delta A(1-t)$, $\eta(t) = \delta^2 \chi(t)$ and
--   $$
--   P_\delta(t) = \begin{pmatrix} d_1(t) + d_2(t)\,\eta(t)^2 & d_2(t)\,\eta(t) \\ d_2(t)\,\eta(t) & d_2(t) \end{pmatrix}, \qquad \widetilde P_\delta(t) = C_\delta\, P_\delta(1-t)\, C_\delta^{\top}, \qquad C_\delta = \begin{pmatrix} 0 & 1 \\ 1 & -\delta^2 \end{pmatrix}.
--   $$
--   The *coordinate cometric* $R_\delta = R^{\rho}_\delta : \mathbb{R} \to \mathbb{R}^{2 \times 2}$ with end flag $\rho \in \{\text{left}, \text{right}\}$ is $R^{\text{left}}_\delta = P_\delta$ and $R^{\text{right}}_\delta = \widetilde P_\delta$; it is a smooth family of symmetric matrices, and $R_\delta'$, $R_\delta''$ denote its first and second derivatives in $t$.
--
--   **Theorem.** For either end flag $\rho$, every $\delta \in \mathbb{R}$ and every $t < 1/4$,
--   $$
--   R_\delta'(t) = \begin{pmatrix} \delta\, a(t) & 0 \\ 0 & 0 \end{pmatrix}.
--   $$
--
--   Near $t = 0$ the cometric is diagonal and only its first entry varies, at rate $\delta a(t)$. In particular $R_\delta'(0) = \operatorname{diag}(\delta a(0), 0)$ with $a(0) = e^{-3/2}$; these endpoint values of the derivative enter the force and timing estimates for geodesics that enter the neck and return.
--
--   **Formalization Note** `coordinateCometric right δ` is $R^{\rho}_\delta$ (`right = false` gives $P_\delta$ = `Cometric.P δ`, `right = true` gives `PEnd δ`); `pairing Q u v` $= u^{\top}Qv$, `qform Q q` $= q^{\top}Qq$, `sqnorm q` $= q_1^2+q_2^2$; Lean indexes the coordinates of $p$ as `p 0`, `p 1`, so $p_1$ is `p 0`. Derivatives are Lean's `deriv`, which are genuine derivatives here because $R_\delta$ is smooth. The cutoff $a$ is `expNegInvGlue (2/3 - u)` and $\sigma$ is `Real.smoothTransition`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Returning.lean#L842-L857

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning

open OAI OAI.ThreeManifold OAI.ThreeManifold.Cometric
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
open Neck Matrix

theorem OAI.ThreeManifold.Cometric.coordinateCometric_end_deriv {right : Bool} {δ t : ℝ} (ht : t < 1 / 4) :
    deriv (coordinateCometric right δ) t = !![δ * a t, 0; 0, 0] := by sorry
