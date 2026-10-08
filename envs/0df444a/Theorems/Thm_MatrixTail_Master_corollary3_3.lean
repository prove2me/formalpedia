-- Prove2me | Theorems.Thm_MatrixTail_Master_corollary3_3
-- name    : MatrixTail.Master.corollary3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:15:09.289583+00:00
-- url     : https://prove2.me/theorems/87960ad7-f8c1-470a-b16f-9716cdc27169
-- title:
--   Corollary 3.3 — E tr exp(H + X) ≤ tr exp(H + log E e^X)
-- statement:
--   Let $H$ be a fixed $d\times d$ complex Hermitian matrix and $X$ a random $d\times d$ complex Hermitian matrix on a probability space, such that the matrix expectation $\mathbb E e^{X}$ exists. Then
--   $$\mathbb E\operatorname{tr}\exp(H+X) \le \operatorname{tr}\exp\bigl(H+\log(\mathbb E e^{X})\bigr).$$
--
--   This describes how expectation interacts with the trace exponential; it is the step that lets the matrix cumulant generating functions of independent summands be pulled out one at a time.
--
--   **Formalization Note.** $\mathbb E e^X$ is the entrywise expectation, and its existence (every entry of $e^X$ integrable) is the paper's standing regularity assumption made explicit; nothing else is assumed. $\mathbb E e^X$ is then positive definite, so its logarithm is the paper's.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 10, Corollary 3.3

import Mathlib
import Definitions.Def_MatrixTail_Master_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Master

/-- **Corollary 3.3.** Tropp, *User-Friendly Tail Bounds for Sums of Random Matrices*, arXiv:1004.4389v7,
p. 10: "Let `H` be a fixed self-adjoint matrix, and let `X` be a random self-adjoint matrix. Then
`E tr exp(H + X) ≤ tr exp(H + log(E e^X))`."

**Formalization Note.**
* Matrices are complex `d × d`; `X` is measurable and Hermitian at every outcome; `P` is a probability measure.
* `E e^X` is the entrywise expectation `mean P (fun ω => mexp (X ω))`, with `e^X = cfc Real.exp X`; its
  existence (every entry of `e^X` integrable, `MatIntegrable`) is the §2.2 regularity made explicit. Without it
  Lean's `mean` would be the zero matrix.
* `log` is `cfc Real.log` and `tr exp(·)` is `trExp`. Under these hypotheses `ω ↦ tr exp(H + X ω)` is
  integrable, so the left side is the paper's expectation; no further hypothesis is added. -/
theorem corollary3_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (X : Ω → Matrix (Fin d) (Fin d) ℂ) (hX_meas : Measurable X) (hX_herm : ∀ ω, (X ω).IsHermitian)
    (hX_int : MatIntegrable P (fun ω => mexp (X ω))) :
    ∫ ω, trExp (H + X ω) ∂P ≤ trExp (H + mlog (mean P (fun ω => mexp (X ω)))) := by sorry

end MatrixTail.Master
