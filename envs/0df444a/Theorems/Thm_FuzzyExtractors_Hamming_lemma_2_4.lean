-- Prove2me | Theorems.Thm_FuzzyExtractors_Hamming_lemma_2_4
-- name    : FuzzyExtractors.Hamming.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:45.079851+00:00
-- url     : https://prove2.me/theorems/3ad5fbf8-c4d7-4a77-9f35-0bf1653f5832
-- title:
--   Lemma 2.4 — generalized leftover hash lemma: $\mathbf{SD}((H_X(W),X,I),(U_\ell,X,I))\le\frac12\sqrt{2^{-\tilde{\mathbf H}_\infty(W\mid I)}2^\ell}$
-- statement:
--   Let $\{H_x:\alpha\to\{0,1\}^\ell\}_{x\in X}$ be a universal family over a finite set $\alpha$, indexed by a finite nonempty set $X$. Then for every pair of random variables $(W,I)$, where $I$ takes values in an arbitrary set and $X$ is uniform and independent of $(W,I)$,
--   $$\mathbf{SD}\big((H_X(W),X,I),\,(U_\ell,X,I)\big)\;\le\;\frac12\sqrt{2^{-\tilde{\mathbf H}_\infty(W\mid I)}\,2^\ell}. \tag{2}$$
--   In particular, for every $m$ and every $\varepsilon>0$, the family is an average-case $(m,\ell,\varepsilon)$-strong extractor whenever
--   $$\ell\;\le\;m-2\log(1/\varepsilon)+2 .$$
--
--   Universal hashing therefore extracts from average min-entropy with no loss beyond the usual $2\log(1/\varepsilon)$; this is what lets a fuzzy extractor be built from a sketch that leaks information.
--
--   **Formalization Note** $\{0,1\}^n$ is generalized to any finite set $\alpha$; the auxiliary variable $I$ ranges over every type. $\varepsilon>0$ is explicit.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, arXiv:cs/0602007v4, Lemma 2.4, eq. (2), p. 10

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

namespace FuzzyExtractors.Hamming

theorem lemma_2_4 {α X : Type} [Fintype α] [Fintype X] [Nonempty X] {ℓ : ℕ}
    (H : X → α → (Fin ℓ → Bool)) (hH : IsUniversal H) :
    (∀ (ι : Type) (WI : PMF (α × ι)),
      statDist (extractLawAux (fun w x => H x w) WI)
          ((extractLawAux (fun w x => H x w) WI).bind
            fun y => (uniformBits ℓ).map fun u => (u, y.2.1, y.2.2))
        ≤ (1 / 2 : ℝ) * Real.sqrt ((2 : ℝ) ^ (-avgMinEntropy WI) * (2 : ℝ) ^ (ℓ : ℝ))) ∧
    (∀ m ε : ℝ, 0 < ε → (ℓ : ℝ) ≤ m - 2 * Real.logb 2 (1 / ε) + 2 →
      IsAvgStrongExtractor m ε (fun w x => H x w)) := by sorry

end FuzzyExtractors.Hamming
