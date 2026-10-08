-- Prove2me | Theorems.Thm_FuzzyExtractors_EditSketch_appendix_E_key_equation
-- name    : FuzzyExtractors.EditSketch.appendix_E_key_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:54.795207+00:00
-- url     : https://prove2.me/theorems/c1653e52-700d-461d-8906-c9868146f5b7
-- title:
--   Appendix E — the key equation $S(z)\sigma(z) \equiv \omega(z) \bmod z^\delta$
-- statement:
--   Let $K$ be a finite field of characteristic $2$, let $M \subseteq K^*$ be the support of a binary word $p$, and let $\delta \ge 0$. With the error locator $\sigma(z) = \prod_{x \in M} (1 - xz)$, the error evaluator $\omega(z) = \sigma(z) \sum_{x \in M} \frac{xz}{1 - xz}$, and the syndrome polynomial $S(z) = \sum_{\ell = 1}^{\delta - 1} p(\alpha^\ell) z^\ell$ where $p(\alpha^\ell) = \sum_{x \in M} x^\ell$,
--   $$S(z)\,\sigma(z) \equiv \omega(z) \pmod{z^\delta}.$$
--
--   This congruence is the *key equation* of Berlekamp's BCH decoding algorithm as adapted in Appendix E: the syndrome, which is public, is tied by it to the unknown error locator, whose roots are the inverses of the elements of $M$.
--
--   **Formalization Note.** $\omega$ is written without division, as $\sum_{x \in M} xz \prod_{y \in M \setminus \{x\}} (1 - yz)$. The congruence modulo $z^\delta$ is stated as divisibility of $S\sigma - \omega$ by $X^\delta$. The paper's text says "we are given $p(\alpha^\ell)$ for $\ell = 1, \dots, \delta$", but $S$ uses only $\ell \le \delta - 1$; we follow the definition of $S$. The binary case of the paper's $q$-ary words is stated. The statement holds for every $\delta$ (at $\delta = 0$ it is trivial), so no lower bound on $\delta$ is imposed.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, Appendix E, proof of Lemma E.1, p. 43

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic

namespace FuzzyExtractors.EditSketch

open Polynomial in
theorem appendix_E_key_equation {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]
    (δ : ℕ) (M : Finset Kˣ) :
    X ^ δ ∣ synPoly δ M * sigma M - omega M := by sorry

end FuzzyExtractors.EditSketch
