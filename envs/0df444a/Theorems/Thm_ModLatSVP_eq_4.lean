-- Prove2me | Theorems.Thm_ModLatSVP_eq_4
-- name    : ModLatSVP.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:31.830603+00:00
-- url     : https://prove2.me/theorems/eabe69e2-a3b0-4dba-9b9e-74a085c352ee
-- title:
--   (4) — compatible metrics are weighted trace norms: $\|xv\|^2=\sum_\sigma w_\sigma|\sigma(x)|^2$
-- statement:
--   Let $K$ be a totally real or CM number field with involution $\star$, and let $M=\mathbb Z^\iota$ be an $\mathcal O_K$-module with a compatible inner product, given by a positive definite Gram matrix $G$ and the action $x\mapsto xv$ of $K$ on $M\otimes\mathbb Q$. For every nonzero $v\in M$ there are weights $w_\sigma>0$, one for each embedding $\sigma:K\to\mathbb C$, such that
--
--   $$\|xv\|^2=\sum_{\sigma}w_\sigma\,|\sigma(x)|^2\qquad\text{for all }x\in K,$$
--
--   and conjugate embeddings carry equal weights: $w_{\bar\sigma}=w_\sigma$.
--
--   So on every line $Kv$ the metric is a weighted canonical (trace) norm. This is what lets the paper compare the minimum and the determinant of a rank-one module (Lemma 2.1).
--
--   Differences from the source:
--   - generalization: (4): positive weights w_σ with ∥xv∥² = Σ_σ w_σ|σ(x)|² → the same, plus w_{conj∘σ} = w_σ for every σ; reason: App. B.1 gives w_σ = σ(β) with β = β⋆, and the proof of Lemma 2.1 uses equal weights on conjugate embeddings; dropping the clause gives (4)
--   - generalization: a module in the input model, with positive definite rational Gram matrix G → any positive definite real Gram matrix G; reason: specializes to rational G by casting; the proof does not use rationality
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), (4), §2.2, p.12 (PDF p.12); derivation App. B.1, p.48; equal weights used in the proof of Lemma 2.1, p.13

import Mathlib
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_lam1
import Definitions.Def_ModLatSVP_IsCompatible

open NumberField Matrix

namespace ModLatSVP

/-- **(4), §2.2, p.12 (derived in App. B.1, p.48): compatible metrics are weighted trace norms.**
Kim, Lee, Son, *Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*,
STOC 2027 submission (manuscript sha256 e7151fad…).

Let `K` be totally real or CM with involution `⋆ = τ`, and let `ℤ^ι` be an `𝒪_K`-module with compatible
Gram matrix `G`. For every nonzero `v ∈ ℤ^ι` there are weights `w_σ > 0`, one per embedding
`σ : K → ℂ`, with `∥xv∥² = Σ_σ w_σ |σ(x)|²` for all `x ∈ K`; moreover conjugate embeddings have equal
weights.

**Formalization Note.** `xv` is `φ(x) v` and its squared length `(φ(x)v)ᵀ G (φ(x)v)`. The clause
`w_{conj ∘ σ} = w_σ` is not displayed in (4); it is the property `w_σ = σ(β)` with `β = β⋆` of App. B.1
that the proof of Lemma 2.1 uses ("For CM fields, conjugate embeddings have equal weights", p.13). -/
theorem eq_4 (K : Type*) [Field K] [NumberField K] (hK : IsTotallyReal K ∨ IsCMField K)
    (τ : K ≃ₐ[ℚ] K) (hτ : IsStar K τ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (φ : K →+* Matrix ι ι ℚ) (hM : IsCompatible K τ G φ)
    (v : ι → ℤ) (hv : v ≠ 0) :
    ∃ w : (K →+* ℂ) → ℝ, (∀ σ, 0 < w σ) ∧ (∀ σ, w (ComplexEmbedding.conjugate σ) = w σ) ∧
      ∀ x : K, qf G ((φ x).map (fun q : ℚ => (q : ℝ)) *ᵥ intVec v) =
        ∑ σ : K →+* ℂ, w σ * ‖σ x‖ ^ 2 := by sorry

end ModLatSVP
