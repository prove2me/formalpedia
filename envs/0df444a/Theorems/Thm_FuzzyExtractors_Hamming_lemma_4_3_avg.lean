-- Prove2me | Theorems.Thm_FuzzyExtractors_Hamming_lemma_4_3_avg
-- name    : FuzzyExtractors.Hamming.lemma_4_3_avg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:52.069009+00:00
-- url     : https://prove2.me/theorems/af1dc6df-b3d8-46e2-9760-2885421c7fe0
-- title:
--   Lemma 4.3, average-case form — sketch plus universal hashing extracts $\ell\le\tilde m-2\log(1/\varepsilon)+2$ bits
-- statement:
--   Let $(\mathsf{SS},\mathsf{Rec})$ be an average-case $(\mathcal M,m,\tilde m,t)$-secure sketch on a finite space $\mathcal M$, let $\{H_x:\mathcal M\to\{0,1\}^\ell\}_{x\in X}$ be a universal family indexed by a finite nonempty set $X$, let $\varepsilon>0$, and suppose
--   $$\ell\;\le\;\tilde m-2\log(1/\varepsilon)+2 .$$
--   Then the construction of Lemma 4.1 with $\mathsf{Ext}(w;x)=H_x(w)$, namely $\mathsf{Gen}(w)=(H_x(w),(\mathsf{SS}(w),x))$ and $\mathsf{Rep}(w',(s,x))=H_x(\mathsf{Rec}(w',s))$, is an average-case $(\mathcal M,m,\ell,t,\varepsilon)$-fuzzy extractor.
--
--   In particular one can extract up to $\tilde m-2\log(1/\varepsilon)+2$ nearly uniform bits from a secure sketch with residual min-entropy $\tilde m$.
--
--   **Formalization Note** This is the sentence "if the above secure sketch is average-case secure, then so is the resulting fuzzy extractor" (p. 14) applied to Lemma 4.3. $\varepsilon>0$ is explicit; $\ell$ is a natural number with $\ell\le\tilde m-2\log(1/\varepsilon)+2$ as a real inequality.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, arXiv:cs/0602007v4, Lemma 4.3 and the following sentence, p. 14

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

namespace FuzzyExtractors.Hamming

theorem lemma_4_3_avg {M S X : Type} [Fintype M] [Fintype X] [Nonempty X] {ℓ : ℕ}
    (dis : M → M → ℕ) (m m' ε : ℝ) (t : ℕ)
    (SS : M → PMF S) (Rec : M → S → PMF M) (hSS : IsAvgSecureSketch dis m m' t SS Rec)
    (H : X → M → (Fin ℓ → Bool)) (hH : IsUniversal H)
    (hε : 0 < ε) (hℓ : (ℓ : ℝ) ≤ m' - 2 * Real.logb 2 (1 / ε) + 2) :
    IsAvgFuzzyExtractor dis m ℓ t ε
      (sketchExtGen SS fun w x => H x w) (sketchExtRep Rec fun w x => H x w) := by sorry

end FuzzyExtractors.Hamming
