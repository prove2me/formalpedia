-- Prove2me | Theorems.Thm_FuzzyExtractors_ImprovedJS_construction_5_step_2
-- name    : FuzzyExtractors.ImprovedJS.construction_5_step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:40.398561+00:00
-- url     : https://prove2.me/theorems/8c13ab2f-1fbc-4556-bdd6-a329e2d76ce5
-- title:
--   Construction 5, Step 2, p. 21 — the sketch entries are the first $t$ elementary symmetric polynomials of $w$, up to sign
-- statement:
--   Let $\mathcal F$ be a field, $t\le s$ natural numbers and $w=\{x_1,\dots,x_s\}\subseteq\mathcal F$ with $|w|=s$. For $k=1,\dots,t$, the coefficient of degree $s-k$ of $p'(z)=\prod_{x\in w}(z-x)$, which is the $k$-th entry of the sketch $\mathsf{SS}(w)$ of Construction 5, equals
--
--   $$(-1)^k\, e_k(x_1,\dots,x_s),\qquad e_k(x_1,\dots,x_s)=\sum_{S\subseteq[s],\,|S|=k}\ \prod_{i\in S}x_i .$$
--
--   This is the paper's remark that outputting the top $t$ coefficients of $p'$ is equivalent to outputting the first $t$ elementary symmetric polynomials of the points of $w$.
--
--   **Formalization Note.** The paper says "equivalent"; the precise relation includes the sign $(-1)^k$, which is stated here. The paper's display writes the second sum as $\sum_{i\neq j}x_ix_j$; we read it as the elementary symmetric polynomial $e_2=\sum_{i<j}x_ix_j$, consistent with the general term $\sum_{|S|=t}\prod_{i\in S}x_i$. In Lean the entry indices are $0$-based ($k$ here is `k + 1` for `k : Fin t`). The paper leaves $t\le s$ implicit; it is a hypothesis here.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, Construction 5, SS Step 2, p. 21

import Mathlib
import Definitions.Def_FuzzyExtractors_ImprovedJS_Basic

namespace FuzzyExtractors.ImprovedJS

/-- Construction 5, Step 2 (p. 21): the sketch entries are, up to sign, the first t elementary
symmetric polynomials of the points of w: the coefficient of degree s − (k + 1) of p′ is
(−1)^(k+1) e_{k+1}(w). -/
theorem construction_5_step_2 {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] (s t : ℕ) (hts : t ≤ s)
    (w : Finset 𝔽) (hw : w.card = s) (k : Fin t) :
    sketchCoeffs s t w k = (-1) ^ ((k : ℕ) + 1) * w.val.esymm ((k : ℕ) + 1) := by sorry

end FuzzyExtractors.ImprovedJS
