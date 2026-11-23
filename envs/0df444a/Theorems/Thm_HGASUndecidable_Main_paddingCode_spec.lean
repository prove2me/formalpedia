-- Prove2me | Theorems.Thm_HGASUndecidable_Main_paddingCode_spec
-- name    : HGASUndecidable.Main.paddingCode_spec
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:27:19.256819+00:00
-- url     : https://prove2.me/theorems/ceff992d-63d5-48d5-b021-fc6e1a92ff5a
-- title:
--   The padding code denotes a valid code for exactly the Lemma 6.1 field
-- statement:
--   Let $(m,3,\mathrm{terms})$ be valid and $m\le n$. Then `paddingCode h j terms` decodes to some valid code $(n,3+2j,\mathrm{outTerms})$, and that code denotes exactly the Lemma 6.1 padding of the input field. In coordinates, the output list represents
--   $$F_i(x)\bigg(\sum_{k<n}x_k^2\bigg)^j\quad(i<m),\qquad -x_i^3\bigg(\sum_{k<n}x_k^2\bigg)^j\quad(m\le i<n),$$
--   so every retained exponent list has total degree $3+2j$. Sortedness and duplicate-freeness follow from canonical exponent serialization, while the real-valued semantic equality follows by mapping the rational multivariate polynomials and clearing denominators.
-- source:
--   Paper #1477, Lemma 6.1 (printed p. 15/PDF 17), equations (2.1) and (2.2) in the proof of Theorem 2.1 (printed pp. 11–12/PDF 13–14), together with the mission's normalized finite code representation.

import Definitions.Def_HGASUndecidable_Main_PaddingCodes

open scoped BigOperators

theorem HGASUndecidable.Main.paddingCode_spec {m n : ℕ} (h : m ≤ n) (j : ℕ)
    (terms : List (ℕ × List ℕ × ℚ))
    (hv : HGASUndecidable.Main.ValidCode (m, 3, terms)) :
    ∃ outTerms : List (ℕ × List ℕ × ℚ),
      HGASUndecidable.Main.decodeField (HGASUndecidable.Main.paddingCode h j terms) =
        some (n, 3+2*j, outTerms) ∧
      HGASUndecidable.Main.ValidCode (n, 3+2*j, outTerms) ∧
      HGASUndecidable.Main.codeField (n, 3+2*j, outTerms) =
        HGASUndecidable.Main.padding h j
          (HGASUndecidable.Main.codeField (m, 3, terms)) := by sorry
