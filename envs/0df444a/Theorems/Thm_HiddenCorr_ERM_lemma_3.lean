-- Prove2me | Theorems.Thm_HiddenCorr_ERM_lemma_3
-- name    : HiddenCorr.ERM.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:35:16.510432+00:00
-- url     : https://prove2.me/theorems/55461649-8e55-413c-b419-292e3f139623
-- title:
--   Lemma 3 — contraction: $\hat{\mathfrak R}_X(\phi\circ F)\le2L\,\hat{\mathfrak R}_X(F)+|\phi(0)|$
-- statement:
--   Let $\phi:\mathbb R\to\mathbb R$ be $L$-Lipschitz and let $F$ be a nonempty class of real-valued functions on $\mathcal X$. For every sample $X=(X_1,\dots,X_n)$,
--   $$\hat{\mathfrak R}_X(\phi\circ F)\le 2L\,\hat{\mathfrak R}_X(F)+|\phi(0)|,$$
--   where $\phi\circ F=\{\phi\circ f:f\in F\}$ and $\hat{\mathfrak R}_X$ is the coefficient-normalized complexity of Definition 2.
--
--   It transfers complexity bounds from a hypothesis class to the loss class when the loss is Lipschitz in the prediction (part 2 of Theorem 8).
--
--   Differences from the source:
--   - encoding: E_ε over independent Rademacher signs, conditional on the sample; complexities possibly infinite → uniform average over all sign vectors (finite sum / 2^n); R̂_X, R̂^vec_X valued in [0, ∞] (ℝ≥0∞); reason: same quantity; ℝ≥0∞ keeps an unbounded class's +∞ value
--   - encoding: L-Lipschitz, L ≥ 0 real → LipschitzWith L φ with L : ℝ≥0; 2L as 2 * (L : ℝ≥0∞) (0 · ∞ = 0); reason: Lean convention; for L = 0, φ is constant and the bound |φ(0)| holds
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 21, Lemma 3

import Mathlib
import Definitions.Def_HiddenCorr_ERM_Complexity

open scoped ENNReal

universe u

namespace HiddenCorr.ERM

/-- **Lemma 3** (contraction), p. 21. Let `φ : ℝ → ℝ` be `L`-Lipschitz and let `F` be a
nonempty class of real-valued functions on `X`. For every sample `X = (X₁, …, Xₙ)`,
`R̂_X(φ ∘ F) ≤ 2L R̂_X(F) + |φ(0)|`, where `φ ∘ F = {φ ∘ f : f ∈ F}`. -/
theorem lemma_3 {𝒳 : Type u} (φ : ℝ → ℝ) (L : NNReal) (hφ : LipschitzWith L φ)
    (F : Set (𝒳 → ℝ)) (hF : F.Nonempty) (n : ℕ) (X : Fin n → 𝒳) :
    radX X ((fun f => φ ∘ f) '' F) ≤ 2 * (L : ℝ≥0∞) * radX X F + ENNReal.ofReal |φ 0| := by sorry

end HiddenCorr.ERM
