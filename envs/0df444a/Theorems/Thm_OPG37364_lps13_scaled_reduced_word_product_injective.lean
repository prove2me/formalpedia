-- Prove2me | Theorems.Thm_OPG37364_lps13_scaled_reduced_word_product_injective
-- name    : OPG37364.lps13_scaled_reduced_word_product_injective
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T04:33:54.97042+00:00
-- url     : https://prove2.me/theorems/e7da13e5-b5dc-41cb-87d4-7fe6d2852aa2
-- title:
--   Injectivity of scaled reduced norm-13 quaternion words
-- statement:
--   Let S be the original fourteen integral Hamilton quaternion generators of norm 13, indexed by Fin 14. A finite word is reduced when no letter is immediately followed by its conjugate. Write Q(w) for its ordered integral quaternion product, with Q([])=1.
--
--   For any natural numbers r,s and any reduced words u,v,
--
--   $$13^r Q(u)=13^s Q(v)\quad\Longrightarrow\quad r=s\ \text{ and }\ u=v.$$
--
--   The equality is literal in the ring of integral Hamilton quaternions, and each power of 13 acts by integer scalar multiplication. Empty words and zero exponents are included. Reducedness is only an adjacent-letter condition; cyclic reduction is not assumed. This is an injectivity statement for this specific generator family, not a factorization or surjectivity theorem for arbitrary quaternions.
-- source:
--   Classical background: Davidoff–Sarnak–Valette, Elementary Number Theory, Group Theory, and Ramanujan Graphs, §2.6 (normal forms) and §4.4.2 (word-count correspondence), https://math.bme.hu/~gabor/oktatas/SztoM/DavidoffSarnakValette.pdf . This fixed-13 formalization uses the supplied last-letter induction and coordinatewise cancellation of 13, reusing the accepted OPG37364 reduced-word primitivity theorem (3e0ddc02-b0be-46f7-a8e1-c4d4d368ead0; accepted submission eff9b353-2b19-4fdc-860f-06240a14b8fa), the original generator definitions, and their proved norm/conjugation identities. No claim of mathematical novelty or of this exact Lean argument appearing in the book is made.

import Definitions.Def_opg37364_lps13_words
set_option autoImplicit false

namespace OPG37364

theorem lps13_scaled_reduced_word_product_injective
    (r s : ℕ) (u v : List (Fin 14))
    (hu : lps13WordReduced u) (hv : lps13WordReduced v)
    (h : (13 : ℤ)^r • lps13WordProduct u = (13 : ℤ)^s • lps13WordProduct v) :
    r = s ∧ u = v := by sorry

end OPG37364
