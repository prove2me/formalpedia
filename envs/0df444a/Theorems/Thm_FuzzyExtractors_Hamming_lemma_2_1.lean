-- Prove2me | Theorems.Thm_FuzzyExtractors_Hamming_lemma_2_1
-- name    : FuzzyExtractors.Hamming.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:58.074974+00:00
-- url     : https://prove2.me/theorems/51b25cb3-57b1-4ff1-b985-3a002f6e528a
-- title:
--   Lemma 2.1 — leftover hash lemma: $\mathbf{SD}((H_X(W),X),(U_\ell,X))\le\frac12\sqrt{2^{-\mathbf H_\infty(W)}2^\ell}$
-- statement:
--   Let $\{H_x:\alpha\to\{0,1\}^\ell\}_{x\in X}$ be a universal family over a finite set $\alpha$, indexed by a finite nonempty set $X$: for all $a\ne b$, $\Pr_{x\in X}[H_x(a)=H_x(b)]=2^{-\ell}$. Then, with $X$ uniform and independent of $W$, for every random variable $W$ on $\alpha$,
--   $$\mathbf{SD}\big((H_X(W),X),\,(U_\ell,X)\big)\;\le\;\frac12\sqrt{2^{-\mathbf H_\infty(W)}\,2^\ell}. \tag{1}$$
--   In particular, for every $m$ and every $\varepsilon>0$, the family is an $(m,\ell,\varepsilon)$-strong extractor (with $\mathsf{Ext}(w;x)=H_x(w)$) whenever
--   $$\ell\;\le\;m-2\log(1/\varepsilon)+2 .$$
--
--   This is the leftover hash (privacy amplification) lemma, the standard way to turn min-entropy into nearly uniform bits.
--
--   **Formalization Note** The paper's input set $\{0,1\}^n$ is generalized to any finite set $\alpha$. $\varepsilon>0$ is explicit because $\log(1/\varepsilon)$ must be defined; the paper leaves it implicit. Universality is the paper's equality $=2^{-\ell}$.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, arXiv:cs/0602007v4, Lemma 2.1, eq. (1), p. 9

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

namespace FuzzyExtractors.Hamming

theorem lemma_2_1 {α X : Type} [Fintype α] [Fintype X] [Nonempty X] {ℓ : ℕ}
    (H : X → α → (Fin ℓ → Bool)) (hH : IsUniversal H) :
    (∀ W : PMF α,
      statDist (extractLaw (fun w x => H x w) W)
          ((extractLaw (fun w x => H x w) W).bind fun y => (uniformBits ℓ).map fun u => (u, y.2))
        ≤ (1 / 2 : ℝ) * Real.sqrt ((2 : ℝ) ^ (-minEntropy W) * (2 : ℝ) ^ (ℓ : ℝ))) ∧
    (∀ m ε : ℝ, 0 < ε → (ℓ : ℝ) ≤ m - 2 * Real.logb 2 (1 / ε) + 2 →
      IsStrongExtractor m ε (fun w x => H x w)) := by sorry

end FuzzyExtractors.Hamming
