-- Prove2me | Theorems.Thm_OAI_SpinAngle_MatrixAnalysis_cell_trace_identity
-- name    : OAI.SpinAngle.MatrixAnalysis.cell_trace_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:16:20.654963+00:00
-- url     : https://prove2.me/theorems/4b9fd5d6-5e3a-46d7-b57f-666d8ab4b019
-- title:
--   Trace identity for the cell matrix $\sqrt{a}\,b^{-1/2}\sqrt{c}$
-- statement:
--   Let $n$ be a finite index set and work with complex $n\times n$ matrices. For a Hermitian matrix $x$ with spectral decomposition $x=\sum_\lambda\lambda P_\lambda$ put
--   $$\sqrt{x}=\sum_{\lambda>0}\sqrt{\lambda}\,P_\lambda,\qquad x^{-1/2}=\sum_{\lambda>0}\lambda^{-1/2}P_\lambda ,$$
--   and let both be $0$ when $x$ is not Hermitian. For positive semidefinite $x$, $\sqrt{x}$ is the usual square root and $x^{-1/2}$ is the pseudo-inverse of $\sqrt{x}$ (the inverse square root on the range of $x$ and $0$ on its kernel).
--
--   **Theorem.** Let $a$ and $c$ be positive semidefinite $n\times n$ matrices and let $b$ be an arbitrary $n\times n$ matrix. With $M=\sqrt{a}\,b^{-1/2}\sqrt{c}$,
--   $$\operatorname{tr}\big(M^{*}M\big)=\operatorname{tr}\big(b^{-1/2}\,a\,b^{-1/2}\,c\big).$$
--
--   The left-hand side is the squared Hilbert–Schmidt norm of $M$, so in particular $\operatorname{tr}(b^{-1/2}ab^{-1/2}c)$ is a nonnegative real number. Matrices of the form $M$ are the cell factors that appear when a product state is normalized by the inverse square root of an averaged state, and the identity computes their contribution to Hilbert–Schmidt, hence operator-norm, bounds.
--
--   **Formalization Note** $\sqrt{x}$ and $x^{-1/2}$ are `MatrixAnalysis.root x = cfc Real.sqrt x` and `MatrixAnalysis.invRoot x = cfc (fun t => (Real.sqrt t)⁻¹) x`. Since `Real.sqrt` vanishes on negative reals and `0⁻¹ = 0`, these give the formulas above, and the continuous functional calculus returns `0` for non-self-adjoint arguments. Positive semidefiniteness is the Loewner condition `0 ≤ a`, and $M^{*}$ is `star M`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/SpinAngle/Core.lean#L3905-L3918

import Mathlib
import Definitions.Def_SpinAngle
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_Core

open OAI OAI.SpinAngle OAI.SpinAngle.MatrixAnalysis
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open scoped BigOperators
open scoped BigOperators
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
open scoped BigOperators
open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type*} [contextInstance3521_21 : Fintype n] [contextInstance3521_33 : DecidableEq n]

theorem OAI.SpinAngle.MatrixAnalysis.cell_trace_identity (a b c : Mat n) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (star (root a * invRoot b * root c) * (root a * invRoot b * root c)).trace =
      (invRoot b * a * invRoot b * c).trace := by sorry
