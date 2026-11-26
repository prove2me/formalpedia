-- Prove2me | Theorems.Thm_LefebvreVariations_symmetric_group_seven_realizable
-- name    : LefebvreVariations.symmetric_group_seven_realizable
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:03:18.72722+00:00
-- url     : https://prove2.me/theorems/29905750-3e09-5372-94c2-e95dc90e9369
-- title:
--   Lefebvre's variations, No. 145 — on a theme by Hilbert: the symmetric group on seven letters is a Galois group over the rationals
-- statement:
--   The symmetric group $S_7$ on seven letters is the Galois group over $\mathbb{Q}$ of a Galois extension: there is a Galois extension $L/\mathbb{Q}$ with
--
--   $$
--   \operatorname{Gal}(L/\mathbb{Q})\;\cong\; S_7 .
--   $$
--
--   One can take $L$ to be the splitting field of $X^7+2X^5-10X^4-26X^3+36X^2+2X-2$. This is the case $S_7$ of the Inverse Galois Problem over $\mathbb{Q}$ for symmetric groups, a classical theorem of Hilbert (1892) for every $S_n$. It is the first symmetric group of prime degree above $S_5$ that is not covered by the existing small cases.
--
--   **Formalization Note.** The statement is `InverseGalois.IsRealizable ℚ (Equiv.Perm (Fin 7))`, with the parent's own definition: a field `L` that is a Galois extension of `ℚ` together with a group isomorphism `Equiv.Perm (Fin 7) ≃* (L ≃ₐ[ℚ] L)`.
--
--   **Why this is a variation.** This varies the open InverseGalois.inverse_galois_problem_symmetric_group (every symmetric group S_n is realizable over Q; Hilbert 1892 proved this on paper, but the platform's formal parent is still Open). It is the case n = 7 with the parent's own definition IsRealizable; the platform already has S_3 and S_5 as variations, and S_7 was absent. It is a finite, explicit instance (the septic X^7+2X^5-10X^4-26X^3+36X^2+2X-2: Eisenstein at 2, five real roots, so one transposition from complex conjugation; 7 prime). There is no formal link to the parent beyond being its n = 7 case.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   D. Hilbert, "Ueber die Irreducibilität ganzer rationaler Functionen mit ganzzahligen Coefficienten", J. reine angew. Math. 110 (1892) 104-129 (bibliographic data verified on EuDML/Wikipedia; that it realizes every S_n over Q is cited from memory). The prime-degree criterion (an irreducible polynomial of prime degree p over Q with exactly two non-real roots has Galois group S_p) is standard, e.g. Dummit and Foote, Abstract Algebra, section 14.6 (section number cited from memory, not re-checked). Numerics checked independently: the septic X^7+2X^5-10X^4-26X^3+36X^2+2X-2 has exactly 5 real roots and is Eisenstein at 2. Origin: the case S_7 of the open platform problem InverseGalois.inverse_galois_problem_symmetric_group; S_3 and S_5 already exist as variations.

import Definitions.Def_InverseGalois_realizability

set_option autoImplicit false

namespace LefebvreVariations

/-- `S₇` is the Galois group over `ℚ` of the irreducible septic `X⁷ + 2X⁵ - 10X⁴ - 26X³ + 36X² + 2X - 2`
(Eisenstein at 2, five real roots, hence one non-real pair, which gives a transposition; a
transitive subgroup of `S₇` containing a transposition is all of `S₇` since `7` is prime): the
symmetric group on seven letters is realizable over `ℚ`. Hilbert (1892) realized every `Sₙ` over
`ℚ`; for the prime-degree criterion see Dummit–Foote, *Abstract Algebra*, §14.6. -/
theorem symmetric_group_seven_realizable :
    InverseGalois.IsRealizable ℚ (Equiv.Perm (Fin 7)) := by
  sorry

end LefebvreVariations
