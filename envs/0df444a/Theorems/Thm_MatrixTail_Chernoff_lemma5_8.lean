-- Prove2me | Theorems.Thm_MatrixTail_Chernoff_lemma5_8
-- name    : MatrixTail.Chernoff.lemma5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:11:15.283885+00:00
-- url     : https://prove2.me/theorems/8999e573-93b1-451b-900f-99e3b5303b3f
-- title:
--   Lemma 5.8 — Chernoff mgf: E e^{θX} ≼ I + (e^θ − 1)·E X for a random psd contraction
-- statement:
--   Let $X$ be a random $d\times d$ complex matrix which is almost surely positive semidefinite with $\lambda_{\max}(X)\le 1$. Then, for every $\theta\in\mathbb R$,
--   $$\mathbb E\,e^{\theta X} \preccurlyeq \mathbf I + (e^{\theta}-1)\,\mathbb E X,$$
--   where $\preccurlyeq$ is the semidefinite order: $A\preccurlyeq B$ means that $B-A$ is positive semidefinite.
--
--   This is the matrix version of the chord bound $e^{\theta x}\le 1+(e^\theta-1)x$ on $[0,1]$, and it controls the matrix moment generating function of each summand in the matrix Chernoff inequality.
--
--   **Formalization Note** The expectation is entrywise; the hypotheses hold almost surely. The entries of $X$ and $e^{\theta X}$ are bounded, so their integrability is implied and not assumed.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 22, Lemma 5.8

import Mathlib
import Definitions.Def_MatrixTail_Chernoff_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Chernoff

/-- **Lemma 5.8 (Chernoff mgf)** (Tropp, arXiv:1004.4389v7, p. 22). Suppose that `X` is a random psd
matrix that satisfies `λmax(X) ≤ 1`. Then `E e^{θX} ≼ I + (e^θ − 1)(E X)` for `θ ∈ ℝ`.

Formalization Note: complex `d × d` matrices; `e^{θX}` is the `cfc` exponential and `E` the entrywise
expectation `mean`; `≼` is Mathlib's Loewner order (`MatrixOrder`), `A ≤ B ↔ (B − A).PosSemidef`.
`X` is measurable (a random matrix) and the hypotheses "psd" and "`λmax(X) ≤ 1`" hold almost surely
(the §2.2 convention of omitting "almost surely"). The entries of `X` and `e^{θX}` are bounded, so their
integrability follows and is not assumed. -/
theorem lemma5_8 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (X : Ω → Matrix (Fin d) (Fin d) ℂ) (hmeas : Measurable X)
    (hpsd : ∀ᵐ ω ∂P, (X ω).PosSemidef) (hle : ∀ᵐ ω ∂P, MatrixTail.Master.lambdaMax (X ω) ≤ 1) (θ : ℝ) :
    MatrixTail.Master.mean P (fun ω => MatrixTail.Master.mexp (θ • X ω)) ≤ 1 + (Real.exp θ - 1) • MatrixTail.Master.mean P X := by sorry

end MatrixTail.Chernoff
