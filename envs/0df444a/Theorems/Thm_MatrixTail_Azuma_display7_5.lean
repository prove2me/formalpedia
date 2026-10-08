-- Prove2me | Theorems.Thm_MatrixTail_Azuma_display7_5
-- name    : MatrixTail.Azuma.display7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:25:14.448743+00:00
-- url     : https://prove2.me/theorems/2c5bbe97-c87c-439d-8e9c-f56d3be9c562
-- title:
--   Display (7.5) — E tr exp(Σ θX_k) ≤ tr exp(2θ² Σ A_k²) for an adapted sequence
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $\mathcal F_0\subset\mathcal F_1\subset\cdots\subset\mathcal F$, and write $\mathbb E_k[\,\cdot\,]=\mathbb E[\,\cdot\mid\mathcal F_k]$. Let $X_1,\dots,X_n$ be random self-adjoint $d\times d$ complex matrices with integrable entries, **adapted** ($X_k$ is $\mathcal F_k$-measurable), and let $A_1,\dots,A_n$ be **fixed** self-adjoint matrices such that, for each $k$,
--   $$
--   \mathbb E_{k-1}X_k = 0 \quad\text{and}\quad X_k^2\preceq A_k^2 \ \text{almost surely}.
--   $$
--   Then for every $\theta\in\mathbb R$,
--   $$
--   \mathbb E\operatorname{tr}\exp\Big(\sum_{k=1}^n\theta X_k\Big) \le \operatorname{tr}\exp\Big(2\theta^2\sum_{k=1}^n A_k^2\Big).
--   $$
--
--   This is the bound on the trace of the matrix moment generating function of a martingale sum from which the matrix Azuma inequality follows. It uses that the bounds $A_k$ are deterministic: they do not depend on the values of the random sequence.
--
--   **Formalization Note** The conditional expectation of a matrix is entrywise, and the sequence is indexed by $k=1,\dots,n$. The $X_k$ are not assumed independent. The left-hand expectation is finite automatically, because $X_k^2\preceq A_k^2$ bounds $\|X_k\|$ by $\|A_k\|$.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 30, display (7.5) (Theorem 7.1, proof)

import Mathlib
import Definitions.Def_MatrixTail_Azuma_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Azuma

/-- **Display (7.5)** (Theorem 7.1, proof, p. 30). Tropp, *User-Friendly Tail Bounds for Sums of Random
Matrices*, arXiv:1004.4389v7, p. 30: "By iteration, we achieve
`E tr exp(Σ_k θX_k) ≤ tr exp(2θ² Σ_k A_k²)`. (7.5) Note that this procedure relies on the fact that the
sequence `{A_k}` of upper bounds does not depend on the values of the random sequence `{X_k}`." Stated under
the hypotheses of Theorem 7.1 (p. 27), for every `θ ∈ ℝ`.

**Formalization Note.**
* **Setting (§7.1, p. 27).** `P` is a probability measure on `(Ω, m0)` and `ℱ` a filtration
  `ℱ 0 ≤ ℱ 1 ≤ ⋯ ≤ m0`. The finite sequence is `X 1, …, X n` (indices `k ∈ Finset.Icc 1 n`; values of `X` and
  `A` outside this range play no role). "Adapted" is: every entry of `X k` is `ℱ k`-strongly measurable.
* `E_{k−1} X_k = 0` is entrywise: `P[X k · i j | ℱ (k − 1)] =ᵐ[P] 0` for all `i, j`; indexing from `1` keeps
  `k − 1` from truncating. The entries of `X k` are integrable (§2.2 regularity; without it Lean's
  conditional expectation is `0` and the centring hypothesis would be empty).
* `X k` is Hermitian at every outcome; `A k` is a fixed (deterministic) Hermitian matrix, and
  `X_k² ≼ A_k²` holds `P`-almost surely (Loewner order under `MatrixOrder`). The `X k` are **not** assumed
  independent.
* Complex `d × d` matrices; `tr exp` is `trExp` (`cfc Real.exp`, real part of the trace).
* No integrability hypothesis on the left integrand: `X_k² ≼ A_k²` a.s. gives `‖X_k‖ ≤ ‖A_k‖` a.s., so
  `ω ↦ tr exp(Σ_k θX_k(ω))` is measurable and almost surely bounded, hence integrable; Lean's junk value
  `0` does not arise. -/
theorem display7_5 {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) {d : ℕ} (n : ℕ)
    (X : ℕ → Ω → Matrix (Fin d) (Fin d) ℂ) (A : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (hX_adapted : ∀ k ∈ Finset.Icc 1 n, ∀ i j, StronglyMeasurable[ℱ k] (fun ω => X k ω i j))
    (hX_herm : ∀ k ∈ Finset.Icc 1 n, ∀ ω, (X k ω).IsHermitian)
    (hX_int : ∀ k ∈ Finset.Icc 1 n, MatIntegrable P (X k))
    (hX_mean : ∀ k ∈ Finset.Icc 1 n, ∀ i j, P[fun ω => X k ω i j | ℱ (k - 1)] =ᵐ[P] 0)
    (hA_herm : ∀ k ∈ Finset.Icc 1 n, (A k).IsHermitian)
    (hXA : ∀ k ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, X k ω ^ 2 ≤ A k ^ 2) (θ : ℝ) :
    ∫ ω, trExp (∑ k ∈ Finset.Icc 1 n, θ • X k ω) ∂P ≤
      trExp ((2 * θ ^ 2) • ∑ k ∈ Finset.Icc 1 n, A k ^ 2) := by sorry

end MatrixTail.Azuma
