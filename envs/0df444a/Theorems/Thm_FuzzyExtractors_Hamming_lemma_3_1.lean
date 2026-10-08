-- Prove2me | Theorems.Thm_FuzzyExtractors_Hamming_lemma_3_1
-- name    : FuzzyExtractors.Hamming.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:15.966982+00:00
-- url     : https://prove2.me/theorems/7807155f-1059-4dfa-b2dd-46fe6378d526
-- title:
--   Lemma 3.1 — a correct sketch with at most $2^\lambda$ outputs is an average-case secure sketch with entropy loss $\lambda$
-- statement:
--   Let $(\mathsf{SS},\mathsf{Rec})$ be randomized procedures on a space $\mathcal M$ with distance $\mathrm{dis}$ that satisfy the correctness property of a secure sketch for some $t$, and suppose the output range of $\mathsf{SS}$ has size at most $2^\lambda$: some finite set $T$ with $|T|\le 2^\lambda$ contains every possible output of $\mathsf{SS}(w)$, for every $w$. Then for every min-entropy threshold $m$,
--   $$(\mathsf{SS},\mathsf{Rec}) \text{ is an average-case } (\mathcal M, m, m-\lambda, t)\text{-secure sketch.}$$
--
--   So the entropy loss of a correct sketch is bounded by its length, uniformly in $m$. This is how the syndrome construction is analysed.
--
--   **Formalization Note** $\lambda$ is real and the sketch takes values in an arbitrary set. The paper's parenthetical case, a sketch that is a $\lambda$-bit string, is an instance of the size hypothesis. "Correctness for some $t$" is the hypothesis that $\mathsf{Rec}(w',s)=w$ whenever $\mathrm{dis}(w,w')\le t$ and $s$ is a possible output of $\mathsf{SS}(w)$.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, arXiv:cs/0602007v4, Lemma 3.1, p. 12

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

namespace FuzzyExtractors.Hamming

theorem lemma_3_1 {M S : Type} (dis : M → M → ℕ) (t : ℕ)
    (SS : M → PMF S) (Rec : M → S → PMF M) (hcorr : SketchCorrect dis t SS Rec) (lam : ℝ)
    (hrange : ∃ T : Finset S, (T.card : ℝ) ≤ (2 : ℝ) ^ lam ∧ ∀ w, (SS w).support ⊆ (T : Set S)) :
    ∀ m : ℝ, IsAvgSecureSketch dis m (m - lam) t SS Rec := by sorry

end FuzzyExtractors.Hamming
