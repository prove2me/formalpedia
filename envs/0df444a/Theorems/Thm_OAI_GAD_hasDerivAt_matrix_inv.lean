-- Prove2me | Theorems.Thm_OAI_GAD_hasDerivAt_matrix_inv
-- name    : OAI.GAD.hasDerivAt_matrix_inv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:07:56.690166+00:00
-- url     : https://prove2.me/theorems/63630f6b-cf10-40b8-9d20-972b6a3dc648
-- title:
--   Derivative of the inverse along a curve of complex matrices: $-A^{-1}HA^{-1}$
-- statement:
--   Let $\iota$ be a finite index set and let $A:\mathbb{R}\to\mathbb{C}^{\iota\times\iota}$ be a curve of square complex matrices that is differentiable at $t\in\mathbb{R}$ with derivative $A'(t)=H$. Assume $\det A(t)\neq0$. Then $s\mapsto A(s)^{-1}$ is differentiable at $t$, and
--
--   $$
--   \frac{d}{ds}\Big|_{s=t}A(s)^{-1}=-A(t)^{-1}\,H\,A(t)^{-1} .
--   $$
--
--   This is the noncommutative version of $(1/a)'=-a'/a^2$: the two factors $A(t)^{-1}$ stand on both sides of $H$. It is the basic tool for computing second derivatives of log-determinant functions along segments of matrices.
--
--   **Formalization Note** The inverse is Mathlib's matrix inverse `(A s)⁻¹`, defined as $\det(A)^{-1}\operatorname{adj}(A)$ and equal to $0$ for singular matrices. Only $\det A(t)\neq0$ is assumed; since the determinant is continuous, $A(s)$ is then invertible for all $s$ near $t$. Matrices carry the entrywise topology.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/MatrixDifferentiation.lean#L86-L106

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation

open OAI OAI.GAD
universe u_1 u_2
open scoped BigOperators
open Matrix
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

theorem OAI.GAD.hasDerivAt_matrix_inv {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (hdet : (A t).det ≠ 0) :
    HasDerivAt (fun s ↦ (A s)⁻¹) (-(A t)⁻¹ * H * (A t)⁻¹) t := by sorry
