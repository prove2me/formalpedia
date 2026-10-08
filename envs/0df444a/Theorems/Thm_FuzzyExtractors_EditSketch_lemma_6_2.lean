-- Prove2me | Theorems.Thm_FuzzyExtractors_EditSketch_lemma_6_2
-- name    : FuzzyExtractors.EditSketch.lemma_6_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:10.897177+00:00
-- url     : https://prove2.me/theorems/be9c5da4-1046-4b13-8d74-1f156f193529
-- title:
--   Lemma 6.2 — a binary word of weight at most $(\delta-1)/2$ is determined by its BCH syndrome
-- statement:
--   Let $K$ be a finite field of characteristic $2$ and $\delta \ge 0$. Let $M, M' \subseteq K^*$ be the supports of two binary words of weight at most $(\delta - 1)/2$. If their syndromes with respect to the binary BCH code of designed distance $\delta$ agree, i.e.
--   $$\sum_{x \in M} x^i = \sum_{x \in M'} x^i \qquad \text{for } i = 1, \dots, \delta - 1,$$
--   then $M = M'$.
--
--   This is the information-theoretic content of the second bullet of Lemma 6.2 (equivalently Lemma E.1(2)): $\mathrm{supp}(x)$ can be computed from $\mathrm{syn}(x)$ when $x$ has weight at most $(\delta - 1)/2$. PinSketch's recovery procedure (Construction 6, step 3) depends on it.
--
--   **Formalization Note.** Both running-time claims of Lemma 6.2 are dropped, since Mathlib has no complexity substrate. The first bullet (computing $\mathrm{syn}(x)$ from $\mathrm{supp}(x)$) is pure computation and has no other content, so it is not stated. The second bullet is stated as injectivity of the syndrome map on light words, which is exactly the existence of a decoder. Only the binary case is stated; the $q$-ary generality of Lemma E.1 is not formalized. The BCH code of length $n = 2^\mu - 1$ is the primitive one, indexed by $K^*$.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, Lemma 6.2 (second bullet), p. 23; Lemma E.1(2), p. 43

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic

namespace FuzzyExtractors.EditSketch

theorem lemma_6_2 {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]
    (δ : ℕ) (M M' : Finset Kˣ) (hM : M.card ≤ (δ - 1) / 2) (hM' : M'.card ≤ (δ - 1) / 2)
    (hsyn : ∀ i : ℕ, 1 ≤ i → i ≤ δ - 1 → syn i M = syn i M') :
    M = M' := by sorry

end FuzzyExtractors.EditSketch
