-- Prove2me | Theorems.Thm_MatrixTail_Azuma_corollary3_3
-- name    : MatrixTail.Azuma.corollary3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:25:20.371828+00:00
-- url     : https://prove2.me/theorems/d6c7fef7-d082-41e7-8282-1ab0dad95604
-- title:
--   Corollary 3.3 — E tr exp(H + X) ≤ tr exp(H + log E e^X)
-- statement:
--   Let $H$ be a fixed self-adjoint $d\times d$ complex matrix and let $X$ be a random self-adjoint $d\times d$ matrix whose exponential $e^{X}$ has integrable entries. Then
--   $$
--   \mathbb E\operatorname{tr}\exp(H+X) \le \operatorname{tr}\exp\big(H+\log(\mathbb E e^{X})\big).
--   $$
--   Here $\mathbb E e^{X}$ is positive definite, so its matrix logarithm is defined.
--
--   This corollary of Lieb's concavity theorem describes how expectation passes through the trace exponential. It is the step that lets the proof of the matrix Azuma inequality move an expectation inside $\operatorname{tr}\exp$, applied conditionally at each step of an iteration.
--
--   **Formalization Note** Exponential and logarithm are defined by the continuous functional calculus and the expectation of a matrix is entrywise. $X$ is measurable and Hermitian at every outcome; the integrability of the entries of $e^X$ is the paper's standing regularity assumption made explicit.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 10, Corollary 3.3

import Mathlib
import Definitions.Def_MatrixTail_Azuma_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Azuma

/-- **Corollary 3.3.** Tropp, *User-Friendly Tail Bounds for Sums of Random Matrices*, arXiv:1004.4389v7,
p. 10: "Let `H` be a fixed self-adjoint matrix, and let `X` be a random self-adjoint matrix. Then
`E tr exp(H + X) ≤ tr exp(H + log(E e^X))`." Restated locally (also a milestone of mission I); the proof of
Theorem 7.1 applies it conditionally on `F_n` (p. 30), a proof step not posed here.

**Formalization Note.**
* Complex Hermitian `d × d` matrices; `exp` and `log` are `cfc Real.exp` and `cfc Real.log` (`mexp`, `mlog`);
  `E e^X` is the entrywise expectation (`mean`), which is positive definite, where `log` is the paper's (2.7).
* `X` is measurable and Hermitian at every outcome; `P` is a probability measure.
* Regularity (§2.2): the entries of `e^X` are integrable, so that `E e^X` exists. No integrability hypothesis is
  put on `ω ↦ tr e^{H + X(ω)}`: it is nonnegative, and the inequality itself shows its expectation is finite,
  so Lean's junk value `0` of a non-integrable integral never arises under these hypotheses. -/
theorem corollary3_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) (X : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hX_meas : Measurable X) (hX_herm : ∀ ω, (X ω).IsHermitian)
    (hX_int : MatIntegrable P (fun ω => mexp (X ω))) :
    ∫ ω, trExp (H + X ω) ∂P ≤ trExp (H + mlog (mean P (fun ω => mexp (X ω)))) := by sorry

end MatrixTail.Azuma
