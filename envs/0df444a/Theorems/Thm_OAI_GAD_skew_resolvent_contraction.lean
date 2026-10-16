-- Prove2me | Theorems.Thm_OAI_GAD_skew_resolvent_contraction
-- name    : OAI.GAD.skew_resolvent_contraction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:10:27.951558+00:00
-- url     : https://prove2.me/theorems/4441c541-8bb4-427e-840b-7a5365407fa0
-- title:
--   The resolvent $(I+K)^{-1}$ of a skew-Hermitian matrix $K$ is a contraction
-- statement:
--   Let $\iota$ be a finite index set and let $K\in\mathbb{C}^{\iota\times\iota}$ be skew-Hermitian, $K^{*}=-K$. The matrix $I+K$ is then invertible; write $R=(I+K)^{-1}$. The theorem states that
--
--   $$
--   I-R^{*}R\succeq0 ,
--   $$
--
--   that is, $I-\bigl((I+K)^{-1}\bigr)^{*}(I+K)^{-1}$ is positive semidefinite. Equivalently, $\|(I+K)^{-1}x\|\le\|x\|$ for every $x\in\mathbb{C}^{\iota}$.
--
--   This contraction property is the matrix inequality behind the comparison of second derivatives of log-determinant functions under a skew-Hermitian shift, which in turn yields convexity of log-determinant deficits.
--
--   **Formalization Note** The statement is `(1 - ((1 + K)⁻¹).conjTranspose * (1 + K)⁻¹).PosSemidef`, with Mathlib's matrix inverse; since $I+K$ is invertible for skew-Hermitian $K$, this is the genuine inverse.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/MatrixDifferentiation.lean#L181-L204

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation

open OAI OAI.GAD
universe u_1 u_2
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

theorem OAI.GAD.skew_resolvent_contraction (K : Matrix ι ι ℂ) (hK : K.conjTranspose = -K) :
    (1 - ((1 + K)⁻¹).conjTranspose * (1 + K)⁻¹).PosSemidef := by sorry
