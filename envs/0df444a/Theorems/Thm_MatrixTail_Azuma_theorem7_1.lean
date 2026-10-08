-- Prove2me | Theorems.Thm_MatrixTail_Azuma_theorem7_1
-- name    : MatrixTail.Azuma.theorem7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:25:08.591612+00:00
-- url     : https://prove2.me/theorems/48565662-2389-4369-89cf-0a91ac38f99f
-- title:
--   Theorem 7.1 (Matrix Azuma) — P{λmax(Σ X_k) ≥ t} ≤ d·e^{−t²/8σ²}, σ² = ‖Σ A_k²‖
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $\mathcal F_0\subset\mathcal F_1\subset\cdots\subset\mathcal F$, and write $\mathbb E_k[\,\cdot\,]=\mathbb E[\,\cdot\mid\mathcal F_k]$. Let $X_1,\dots,X_n$ be an adapted sequence of random self-adjoint $d\times d$ complex matrices ($d\ge1$) with integrable entries, and let $A_1,\dots,A_n$ be a fixed sequence of self-adjoint matrices such that
--   $$
--   \mathbb E_{k-1}X_k = 0 \quad\text{and}\quad X_k^2\preceq A_k^2 \ \text{almost surely}.
--   $$
--   Define the variance parameter $\sigma^2 := \big\|\sum_k A_k^2\big\|$ (spectral norm). Then for all $t\ge 0$,
--   $$
--   \mathbb P\Big\{\lambda_{\max}\Big(\sum_{k=1}^n X_k\Big)\ge t\Big\} \le d\cdot e^{-t^2/8\sigma^2}.
--   $$
--
--   This is the **matrix Azuma inequality**: a matrix martingale difference sequence with deterministic semidefinite bounds on its squares has a subgaussian maximum-eigenvalue tail, with variance parameter the norm of the sum $\sum_k A_k^2$ rather than the sum of the norms, and a dimensional factor $d$. With independent summands it gives a matrix Hoeffding inequality.
--
--   **Formalization Note** Conditional expectations and expectations of matrices are entrywise; adaptedness is entrywise strong measurability. The summands are indexed by $k=1,\dots,n$ so that $\mathcal F_{k-1}$ is well defined. When $\sigma^2=0$ the Lean expression $t^2/0$ equals $0$ and the bound reads $d$, which is true; the paper's reading $e^{-\infty}=0$ also holds there, since every $X_k$ then vanishes almost surely.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 27, Theorem 7.1 (Matrix Azuma), (7.1)–(7.2)

import Mathlib
import Definitions.Def_MatrixTail_Azuma_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Azuma

/-- **Theorem 7.1 (Matrix Azuma).** Tropp, *User-Friendly Tail Bounds for Sums of Random Matrices*,
arXiv:1004.4389v7, p. 27: "Consider a finite adapted sequence `{X_k}` of self-adjoint matrices in dimension
`d`, and a fixed sequence `{A_k}` of self-adjoint matrices that satisfy `E_{k−1} X_k = 0` and
`X_k² ≼ A_k²` almost surely. Compute the variance parameter `σ² := ‖Σ_k A_k²‖`. (7.1) Then, for all
`t ≥ 0`, `P{λmax(Σ_k X_k) ≥ t} ≤ d · e^{−t²/8σ²}`. (7.2)"

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
* Complex `d × d` matrices with `d ≥ 1` (`[NeZero d]`): at `d = 0`, `λmax = sSup ∅ = 0` and the bound
  `0` would be false at `t = 0`. `σ²` is `specNorm (Σ_k A_k²)`, the spectral norm, exactly as (7.1)
  writes it.
* The constant is `1/8` (the paper's Remarks 7.4 and 7.8 improve it to `1/2` only under extra assumptions).
* Degenerate case `σ² = 0`: Lean's `t²/0 = 0` makes the right side `d ≥ 1`, a true and trivial bound;
  the paper's `e^{−∞} = 0` reading at `t > 0` is also true there (then every `A_k² = 0`, so `X_k = 0`
  a.s.), so nothing of content is lost and no positivity hypothesis is added. -/
theorem theorem7_1 {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) {d : ℕ} [NeZero d] (n : ℕ)
    (X : ℕ → Ω → Matrix (Fin d) (Fin d) ℂ) (A : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (hX_adapted : ∀ k ∈ Finset.Icc 1 n, ∀ i j, StronglyMeasurable[ℱ k] (fun ω => X k ω i j))
    (hX_herm : ∀ k ∈ Finset.Icc 1 n, ∀ ω, (X k ω).IsHermitian)
    (hX_int : ∀ k ∈ Finset.Icc 1 n, MatIntegrable P (X k))
    (hX_mean : ∀ k ∈ Finset.Icc 1 n, ∀ i j, P[fun ω => X k ω i j | ℱ (k - 1)] =ᵐ[P] 0)
    (hA_herm : ∀ k ∈ Finset.Icc 1 n, (A k).IsHermitian)
    (hXA : ∀ k ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, X k ω ^ 2 ≤ A k ^ 2) (t : ℝ) (ht : 0 ≤ t) :
    P.real {ω | t ≤ lambdaMax (∑ k ∈ Finset.Icc 1 n, X k ω)} ≤
      d * Real.exp (-t ^ 2 / (8 * specNorm (∑ k ∈ Finset.Icc 1 n, A k ^ 2))) := by sorry

end MatrixTail.Azuma
