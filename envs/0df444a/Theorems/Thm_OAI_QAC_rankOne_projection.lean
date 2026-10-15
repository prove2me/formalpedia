-- Prove2me | Theorems.Thm_OAI_QAC_rankOne_projection
-- name    : OAI.QAC.rankOne_projection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:30:55.933502+00:00
-- url     : https://prove2.me/theorems/266508d8-f357-40a5-9a0c-a7dfa7915243
-- title:
--   A unit qubit vector gives a rank-one orthogonal projection
-- statement:
--   Let $v=(v_0,v_1)\in\mathbb{C}^2$ be a unit vector, $|v_0|^2+|v_1|^2=1$, and let $|v\rangle\langle v|$ denote the $2\times2$ complex matrix with entries $\bigl(|v\rangle\langle v|\bigr)_{xy}=v_x\overline{v_y}$ for $x,y\in\{0,1\}$. Then $|v\rangle\langle v|$ is an orthogonal projection, that is, an idempotent self-adjoint matrix:
--
--   $$
--   \bigl(|v\rangle\langle v|\bigr)^2=|v\rangle\langle v|\qquad\text{and}\qquad\bigl(|v\rangle\langle v|\bigr)^{*}=|v\rangle\langle v| .
--   $$
--
--   This is the one-qubit building block of all product projections in the analysis of constant-depth quantum circuits: the zero and pattern projections of a count are tensor products of such projections, their complements $I-|v\rangle\langle v|$ and identities, and are therefore projections themselves.
--
--   **Formalization Note** The conclusion is `IsStarProjection (rankOne v)`: idempotent and self-adjoint for the conjugate-transpose star on `Matrix Bit Bit ℂ`. The normalization hypothesis is `∑ b, Complex.normSq (v b) = 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/ProductProjection.lean#L75-L87

import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

theorem OAI.QAC.rankOne_projection {v : Bit → ℂ} (hv : ∑ b, Complex.normSq (v b) = 1) :
    IsStarProjection (rankOne v) := by sorry
