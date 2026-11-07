-- Prove2me | Theorems.Thm_LowAccLTC_lemma_2_19_hdx_code_distance
-- name    : LowAccLTC.lemma_2_19_hdx_code_distance
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:24.795021+00:00
-- url     : https://prove2.me/theorems/511cec72-42b5-438c-9322-7935d7e6cd64
-- title:
--   Lemma 2.19 [DLZ25] — distance of HDX codes (corrected: positive parts of the factors)
-- statement:
--   Let $X$ be a weighted pure simplicial complex of rank $r$ that is a $\lambda$-one-sided spectral HDX with $0\le\lambda\le1$, and let $\{C_t\}_{t\in X\langle r-1\rangle}$ be local codes, each of distance at least $\delta\ge0$. Then for every $0\le k<r$ and every face $s\in X\langle k\rangle$, the induced code $C_s$ has relative distance at least
--   $$\prod_{i=0}^{r-k-1}\max(\delta-i\lambda,\,0).$$
--
--   For KMS codes ($\lambda\le4/\sqrt p$, $\delta=1-d/p$) all factors are positive and this gives assumption 3 of Theorem 4.1.
--
--   Differences from the source:
--   - correction: relative distance at least ∏_{i=0}^{r−k−1} (δ − iλ) → ∏_{i=0}^{r−k−1} max(δ − iλ, 0); reason: the printed bound is false when an even number of factors is negative: the complete 3-partite complex with parts of size 2 (uniform μ) is a 1-one-sided HDX, all-words codes on its 2-point lines have δ = 1/2, and for k = 0 the printed bound is (1/2)(−1/2)(−3/2) = 3/8 while C_∅ (all words on 8 top faces) has two codewords at distance 1/8; the correction agrees with the printed bound whenever all factors are nonnegative, which is the paper's only use
--   - encoding: an r-rank simplicial complex with a measure μ on top faces, λ ∈ [0,1] → PureComplex (top faces with r-element vertex sets, positive μ) and the hypothesis 0 ≤ λ ≤ 1; reason: Definition 2.12 and Definition 2.16's range of λ
--   - encoding: λ₂ of the link graph's random-walk operator is at most λ → the variational form E_{(u,v)} g(u)g(v) ≤ λ E g² for every g of mean 0 under the link's vertex law; reason: equivalent by self-adjointness and Courant–Fischer
--   - encoding: codes with distance δ → HasDistAtLeast: distinct codewords disagree with probability ≥ δ; reason: the paper's 'distance at least' (lower-bound) usage
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Lemma 2.19 ([DLZ25]), p.18 (PDF p.21)

import Definitions.Def_LowAccLTC_PureComplex

namespace LowAccLTC

/-- **Lemma 2.19** ([DLZ25]; Ben Yaacov–Dikstein–Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs* (manuscript, sha256 04242e17…), p.18 = PDF p.21), corrected: positive parts of the factors.

Let `X` be a rank-`r` `λ`-one-sided HDX (`0 ≤ λ ≤ 1`), a weighted pure simplicial complex, and let
`{C_t}_{t ∈ X⟨r-1⟩}` be local codes with distance at least `δ ≥ 0`. For every `0 ≤ k < r` and
every `s ∈ X⟨k⟩`, the induced code `C_s` has relative distance at least
`∏_{i=0}^{r-k-1} max(δ - iλ, 0)`.

**Formalization Note.** The printed product `∏ (δ - iλ)` is false when an even number of its
factors is negative; the correction replaces each factor by its positive part. -/
theorem lemma_2_19_hdx_code_distance {r : ℕ} {V T A : Type*} [Fintype T]
    (X : PureComplex r V T) (C₀ : (u : Finset V) → Set (X.star u → A)) (lam δ : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 1) (hX : X.IsOneSidedLocalSpectral lam) (hδ : 0 ≤ δ)
    (hC : ∀ u, X.IsFace u → u.card + 1 = r →
      X.HasDistAtLeast (X.star u) {h | (fun x : X.star u => h x.1) ∈ C₀ u} δ) :
    ∀ s, X.IsFace s → s.card < r →
      X.HasDistAtLeast (X.star s) (X.localCode C₀ s)
        (∏ i ∈ Finset.range (r - s.card), max (δ - i * lam) 0) := by sorry

end LowAccLTC
