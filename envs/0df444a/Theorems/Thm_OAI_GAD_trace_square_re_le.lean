-- Prove2me | Theorems.Thm_OAI_GAD_trace_square_re_le
-- name    : OAI.GAD.trace_square_re_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:09:54.291334+00:00
-- url     : https://prove2.me/theorems/e50f818e-8cd5-4b9a-9099-6e05395df91d
-- title:
--   The real part of $\operatorname{tr}(B^2)$ is at most $\operatorname{Re}\operatorname{tr}(B^{*}B)$
-- statement:
--   Let $\iota$ be a finite index set and let $B\in\mathbb{C}^{\iota\times\iota}$ be any square complex matrix, with conjugate transpose $B^{*}$. Then
--
--   $$
--   \operatorname{Re}\operatorname{tr}\bigl(B^2\bigr)\;\le\;\operatorname{Re}\operatorname{tr}\bigl(B^{*}B\bigr).
--   $$
--
--   The right-hand side is the squared Frobenius (Hilbert–Schmidt) norm $\sum_{i,j}|B_{ij}|^2$, so the inequality bounds the real part of the trace of the square of an arbitrary, possibly non-normal, matrix by its squared Frobenius norm; for Hermitian $B$ both sides coincide. It is used when comparing second derivatives of log-determinant functions, where traces of squares of non-Hermitian products must be estimated.
--
--   **Formalization Note** The statement is phrased entirely through traces, `(Matrix.trace (B * B)).re ≤ (Matrix.trace (B.conjTranspose * B)).re`, which avoids choosing a matrix norm; no decidable equality on $\iota$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/MatrixDifferentiation.lean#L147-L166

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

omit [DecidableEq ι] in
theorem OAI.GAD.trace_square_re_le (B : Matrix ι ι ℂ) :
    (Matrix.trace (B * B)).re ≤ (Matrix.trace (B.conjTranspose * B)).re := by sorry
