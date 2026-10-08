-- Prove2me | Theorems.Thm_MatrixTail_Master_lemma3_4
-- name    : MatrixTail.Master.lemma3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:15:08.416978+00:00
-- url     : https://prove2.me/theorems/3d597a53-003d-44e3-851b-6fa98c3b33c7
-- title:
--   Lemma 3.4 — subadditivity of matrix cgfs: E tr exp(Σ θX_k) ≤ tr exp(Σ log E e^{θX_k})
-- statement:
--   Let $X_1,\dots,X_n$ be independent random $d\times d$ complex Hermitian matrices on a probability space, and let $\theta\in\mathbb R$ be such that every matrix moment generating function $\mathbb E e^{\theta X_k}$ exists. Then
--   $$\mathbb E\operatorname{tr}\exp\Bigl(\sum_{k}\theta X_k\Bigr) \le \operatorname{tr}\exp\Bigl(\sum_k \log\mathbb E e^{\theta X_k}\Bigr).$$
--
--   In terms of the matrix cumulant generating function $\Xi_X(\theta)=\log\mathbb E e^{\theta X}$ this reads $\operatorname{tr}\exp\bigl(\Xi_{\sum_k X_k}(\theta)\bigr)\le\operatorname{tr}\exp\bigl(\sum_k\Xi_{X_k}(\theta)\bigr)$ (Remark 3.5): the matrix replacement for the additivity of scalar cumulant generating functions of independent sums.
--
--   **Formalization Note.** $\theta$ ranges over all reals, as in the paper. Expectations are entrywise, and the existence of each $\mathbb E e^{\theta X_k}$ (every entry integrable) is the only regularity assumed.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 11, Lemma 3.4

import Mathlib
import Definitions.Def_MatrixTail_Master_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Master

/-- **Lemma 3.4 (Subadditivity of Matrix cgfs).** Tropp, *User-Friendly Tail Bounds for Sums of Random
Matrices*, arXiv:1004.4389v7, p. 11: "Consider a finite sequence `{X_k}` of independent, random, self-adjoint
matrices. Then `E tr exp(Σ_k θX_k) ≤ tr exp(Σ_k log E e^{θX_k})` for `θ ∈ ℝ`."

**Formalization Note.**
* The finite sequence is `X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ` (complex matrices), each `X k`
  measurable and Hermitian at every outcome, jointly independent (`iIndepFun X P`) under a probability
  measure `P`.
* `θ` ranges over all of `ℝ`, as on the page. `E e^{θX_k}` is the entrywise expectation
  `mean P (fun ω => mexp (θ • X k ω))`; its existence for this `θ` (`MatIntegrable`) is the §2.2 regularity
  made explicit, and is the only regularity assumed. Without it Lean's `mean` would be the zero matrix.
* `exp`/`log` are `cfc Real.exp`/`cfc Real.log`; `tr exp(·)` is `trExp`.
* The printed proof conditions on `X₁, …, X_k`; the statement itself involves no conditional expectation. -/
theorem lemma3_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d n : ℕ} (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hX_meas : ∀ k, Measurable (X k)) (hX_herm : ∀ k ω, (X k ω).IsHermitian)
    (hX_indep : iIndepFun X P)
    (θ : ℝ) (hX_int : ∀ k, MatIntegrable P (fun ω => mexp (θ • X k ω))) :
    ∫ ω, trExp (∑ k, θ • X k ω) ∂P ≤ trExp (∑ k, mlog (mean P (fun ω => mexp (θ • X k ω)))) := by sorry

end MatrixTail.Master
