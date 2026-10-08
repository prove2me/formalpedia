-- Prove2me | Theorems.Thm_FuzzyExtractors_Hamming_lemma_4_1_avg
-- name    : FuzzyExtractors.Hamming.lemma_4_1_avg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:27.368975+00:00
-- url     : https://prove2.me/theorems/8e5ca6e4-49fe-4630-a747-196b8f19823d
-- title:
--   Lemma 4.1, average-case form — an average-case secure sketch plus an average-case strong extractor gives an average-case fuzzy extractor
-- statement:
--   Let $(\mathsf{SS},\mathsf{Rec})$ be an average-case $(\mathcal M,m,\tilde m,t)$-secure sketch and let $\mathsf{Ext}:\mathcal M\times X\to\{0,1\}^\ell$ be an average-case $(\tilde m,\ell,\varepsilon)$-strong extractor with seed uniform on the finite nonempty set $X$. Define
--   - $\mathsf{Gen}(w;r,x)$: set $P=(\mathsf{SS}(w;r),x)$, $R=\mathsf{Ext}(w;x)$, and output $(R,P)$, with a fresh uniform seed $x$;
--   - $\mathsf{Rep}(w',(s,x))$: recover $w=\mathsf{Rec}(w',s)$ and output $R=\mathsf{Ext}(w;x)$.
--
--   Then
--   $$(\mathsf{Gen},\mathsf{Rep}) \text{ is an average-case } (\mathcal M,m,\ell,t,\varepsilon)\text{-fuzzy extractor.}$$
--
--   The printed Lemma 4.1 is the worst-case-input version; the paper states on p. 14 that it "hold[s] (with the same proofs) for building average-case fuzzy extractors from average-case secure sketches", and that is the form stated here and used by Theorem 5.2.
--
--   **Formalization Note** The extractor acts on $\mathcal M$ directly; the paper's assumption that elements of $\mathcal M$ are represented by $n$ bits is not needed. The seed set is any finite nonempty set.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, arXiv:cs/0602007v4, Lemma 4.1, p. 13, and its average-case form, p. 14 ("Both Lemma 4.1 and Corollary 4.2 hold ... average-case")

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

namespace FuzzyExtractors.Hamming

theorem lemma_4_1_avg {M S X : Type} [Fintype X] [Nonempty X] {ℓ : ℕ}
    (dis : M → M → ℕ) (m m' ε : ℝ) (t : ℕ)
    (SS : M → PMF S) (Rec : M → S → PMF M) (hSS : IsAvgSecureSketch dis m m' t SS Rec)
    (Ext : M → X → (Fin ℓ → Bool)) (hExt : IsAvgStrongExtractor m' ε Ext) :
    IsAvgFuzzyExtractor dis m ℓ t ε (sketchExtGen SS Ext) (sketchExtRep Rec Ext) := by sorry

end FuzzyExtractors.Hamming
