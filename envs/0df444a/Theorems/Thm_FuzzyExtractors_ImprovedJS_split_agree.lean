-- Prove2me | Theorems.Thm_FuzzyExtractors_ImprovedJS_split_agree
-- name    : FuzzyExtractors.ImprovedJS.split_agree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:36.730315+00:00
-- url     : https://prove2.me/theorems/6b612c2d-66c6-4167-84e4-88dfa8da59c4
-- title:
--   §6.2, p. 21 — $p' = p_{\mathrm{high}} + q$ with $\deg q \le s-t-1$, and $p_{\mathrm{high}}$, $-q$ agree on $w$
-- statement:
--   Let $\mathcal F$ be a field, $t\le s$ natural numbers and $w\subseteq\mathcal F$ a set with $|w|=s$. Let $p'(z)=\prod_{x\in w}(z-x)$ and let $p_{\mathrm{high}}(z)=z^s+\sum_{i=s-t}^{s-1}a_iz^i$ be built from the sketch $\mathsf{SS}(w)=(a_{s-1},\dots,a_{s-t})$ of Construction 5, the coefficients of $p'$ of degree $s-1$ down to $s-t$. Then there is a polynomial $q$ with
--
--   $$p' = p_{\mathrm{high}} + q,\qquad \deg q\le s-t-1,\qquad p_{\mathrm{high}}(x) = -q(x)\ \text{ for all } x\in w.$$
--
--   This is the first step of the paper's correctness argument for Construction 5: the decoder knows $p_{\mathrm{high}}$, and on the points of $w$ its values are those of the low-degree polynomial $-q$.
--
--   **Formalization Note.** "$\deg q\le s-t-1$" is `q.degree < s - t`, which forces $q=0$ when $t=s$. The paper leaves $t\le s$ implicit; it is a hypothesis here.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, §6.2, analysis of Construction 5, p. 21, "We can write p′ as p_high + q … agree at all points in w"

import Mathlib
import Definitions.Def_FuzzyExtractors_ImprovedJS_Basic
open Polynomial

namespace FuzzyExtractors.ImprovedJS

/-- Construction 5 analysis (p. 21): p′ = p_high + q with deg q ≤ s − t − 1, and p_high, −q agree
on every point of w. -/
theorem split_agree {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] (s t : ℕ) (hts : t ≤ s)
    (w : Finset 𝔽) (hw : w.card = s) :
    ∃ q : 𝔽[X], charPoly w = pHigh s t (sketchCoeffs s t w) + q ∧
      q.degree < ((s - t : ℕ) : WithBot ℕ) ∧
      ∀ x ∈ w, (pHigh s t (sketchCoeffs s t w)).eval x = -(q.eval x) := by sorry

end FuzzyExtractors.ImprovedJS
