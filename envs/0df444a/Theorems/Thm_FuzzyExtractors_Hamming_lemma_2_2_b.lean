-- Prove2me | Theorems.Thm_FuzzyExtractors_Hamming_lemma_2_2_b
-- name    : FuzzyExtractors.Hamming.lemma_2_2_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:09.009621+00:00
-- url     : https://prove2.me/theorems/d1e35a71-0ee0-4c9a-800a-aee54738c2a3
-- title:
--   Lemma 2.2(b) — conditioning on B with at most $2^\lambda$ values costs at most $\lambda$ bits of average min-entropy
-- statement:
--   Let $A,B,C$ be random variables with a joint law, and suppose $B$ takes at most $2^\lambda$ values: there is a finite set $T$ with $|T|\le 2^\lambda$ containing every possible value of $B$. Then
--   $$\tilde{\mathbf H}_\infty(A\mid(B,C)) \;\ge\; \tilde{\mathbf H}_\infty((A,B)\mid C)-\lambda \;\ge\; \tilde{\mathbf H}_\infty(A\mid C)-\lambda .$$
--   In particular,
--   $$\tilde{\mathbf H}_\infty(A\mid B)\;\ge\;\mathbf H_\infty((A,B))-\lambda\;\ge\;\mathbf H_\infty(A)-\lambda .$$
--
--   This is the basic accounting rule for leaked information: publishing a value with at most $2^\lambda$ possibilities lowers the adversary's average min-entropy by at most $\lambda$. It yields Lemma 3.1 and the security bound of Lemma 4.5.
--
--   **Formalization Note** One joint law of $(A,B,C)$ is given; the laws of $(A,B)$, $(A,C)$, $((A,B),C)$ and $A$ are its images. The "in particular" sentence is stated for the $(A,B)$-marginal of the same law, which covers every pair $(A,B)$ (take $C$ constant). $\lambda$ is a real number and "at most $2^\lambda$ values" is read as a finite set of size at most $2^\lambda$ containing the support of $B$.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, arXiv:cs/0602007v4, Lemma 2.2(b), p. 10 (preamble p. 9)

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

namespace FuzzyExtractors.Hamming

theorem lemma_2_2_b {α β γ : Type} (ABC : PMF (α × β × γ)) (lam : ℝ)
    (hB : ∃ T : Finset β, (T.card : ℝ) ≤ (2 : ℝ) ^ lam ∧ ∀ x ∈ ABC.support, x.2.1 ∈ T) :
    (avgMinEntropy ABC ≥ avgMinEntropy (ABC.map fun x => ((x.1, x.2.1), x.2.2)) - lam ∧
      avgMinEntropy (ABC.map fun x => ((x.1, x.2.1), x.2.2)) - lam ≥
        avgMinEntropy (ABC.map fun x => (x.1, x.2.2)) - lam) ∧
    (avgMinEntropy (ABC.map fun x => (x.1, x.2.1)) ≥
        minEntropy (ABC.map fun x => (x.1, x.2.1)) - lam ∧
      minEntropy (ABC.map fun x => (x.1, x.2.1)) - lam ≥
        minEntropy (ABC.map fun x => x.1) - lam) := by sorry

end FuzzyExtractors.Hamming
