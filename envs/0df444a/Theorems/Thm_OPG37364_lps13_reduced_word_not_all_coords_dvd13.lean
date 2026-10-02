-- Prove2me | Theorems.Thm_OPG37364_lps13_reduced_word_not_all_coords_dvd13
-- name    : OPG37364.lps13_reduced_word_not_all_coords_dvd13
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-10T12:13:11.602985+00:00
-- url     : https://prove2.me/theorems/3e0ddc02-b0be-46f7-a8e1-c4d4d368ead0
-- title:
--   13-primitivity of every reduced LPS13 quaternion word
-- statement:
--   Let w be any finite reduced word in the original fourteen integral norm-13 quaternion generators. Reduced means only that no letter is immediately followed by its conjugate generator. Write its ordered product as Q(w)=a₀+a₁i+a₂j+a₃k. Then
--
--   $$\neg\bigl(13\mid a_0\;\land\;13\mid a_1\;\land\;13\mid a_2\;\land\;13\mid a_3\bigr).$$
--
--   This holds for every word length, including the empty word. Thus every reduced word product is 13-primitive. No graph modulus occurs, and no cyclic reduction, pairwise distinctness, normal form, freeness, connectedness, girth or LPS theorem is assumed. The conclusion does not assert that the coordinate gcd is one or that quaternion factorization is unique.
-- source:
--   Classical reduced-word context: Davidoff–Sarnak–Valette, Definition 2.6.12 and Theorem 2.6.13 (printed pp.68–69), https://math.bme.hu/~gabor/oktatas/SztoM/DavidoffSarnakValette.pdf ; Xavier Dahan, Regular graphs of large girth and arbitrary degree, arXiv:1110.5259v4, Theorem 2.2, https://arxiv.org/pdf/1110.5259v4 . The fixed-modulus-13 outer-product proof used here is a direct implementation-oriented derivation. The supplied factor table is rechecked in Lean; it is not claimed to be a table or proof printed in those sources. No mathematical novelty or full unique-factorization claim is made.

import Definitions.Def_opg37364_lps13_words
set_option autoImplicit false

namespace OPG37364

theorem lps13_reduced_word_not_all_coords_dvd13
    (w : List (Fin 14)) (h : lps13WordReduced w) :
    ¬ ((13 : ℤ) ∣ (lps13WordProduct w).re ∧
      13 ∣ (lps13WordProduct w).imI ∧ 13 ∣ (lps13WordProduct w).imJ ∧
      13 ∣ (lps13WordProduct w).imK) := by sorry

end OPG37364
