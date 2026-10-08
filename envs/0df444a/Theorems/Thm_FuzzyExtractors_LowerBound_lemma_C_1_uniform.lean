-- Prove2me | Theorems.Thm_FuzzyExtractors_LowerBound_lemma_C_1_uniform
-- name    : FuzzyExtractors.LowerBound.lemma_C_1_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:35.121846+00:00
-- url     : https://prove2.me/theorems/3e6ab47c-cbac-457b-97c1-9f789845e8ad
-- title:
--   Lemma C.1 (second sentence) — for uniform passwords, m′ ≤ log K(𝓜, t)
-- statement:
--   Let $\mathcal M$ be a nonempty finite metric space with integer-valued distance $\mathrm{dis}$. If $(\mathsf{SS},\mathsf{Rec})$ is an $(\mathcal M,m,m',t)$-secure sketch with $m=\log|\mathcal M|$ (the password is truly uniform), then
--   $$m' \le \log K(\mathcal M,t),$$
--   where $K(\mathcal M,t)$ is the largest size of an $(\mathcal M,K,t)$-code.
--
--   The residual entropy of a sketch for uniform inputs is bounded by the logarithm of the best code size, so sketches built from optimal codes have optimal entropy loss.
--
--   **Formalization Note** The metric axioms of §2.1 are stated explicitly; nonemptiness of $\mathcal M$ is implicit in the paper (for empty $\mathcal M$ no distribution exists and the claim fails). $K(\mathcal M,t)$ is `K dis t Finset.univ`.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, Lemma C.1 (second sentence), p. 40

import Mathlib
import Definitions.Def_FuzzyExtractors_LowerBound_Basic

namespace FuzzyExtractors.LowerBound

/-- Lemma C.1, second sentence (Appendix C, p. 40): when `m = log |𝓜|`, an (𝓜, m, m', t)-secure
sketch has `m' ≤ log K(𝓜, t)`. -/
theorem lemma_C_1_uniform {M V : Type} [Fintype M] [Nonempty M] (dis : M → M → ℕ)
    (hzero : ∀ x y, dis x y = 0 ↔ x = y)
    (hsymm : ∀ x y, dis x y = dis y x)
    (htri : ∀ x y z, dis x z ≤ dis x y + dis y z)
    (m m' : ℝ) (t : ℕ)
    (SS : M → PMF V) (Rec : M → V → PMF M) (hSS : FuzzyExtractors.Hamming.IsSecureSketch dis m m' t SS Rec)
    (hm : m = Real.logb 2 (Fintype.card M)) :
    m' ≤ Real.logb 2 (K dis t Finset.univ) := by sorry

end FuzzyExtractors.LowerBound
