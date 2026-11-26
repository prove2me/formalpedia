-- Prove2me | Theorems.Thm_LefebvreVariations_fano_not_gf_representable_of_odd
-- name    : LefebvreVariations.fano_not_gf_representable_of_odd
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T23:13:27.836845+00:00
-- url     : https://prove2.me/theorems/30bb194e-bc40-436a-8158-b166f3ac3523
-- title:
--   Lefebvre's variations, No. 36 — on a theme by Rota: the Fano matroid is not representable over odd characteristic
-- statement:
--   This shows that the Fano matroid is an obstruction to representability over fields of odd characteristic.
--
--   Let $q=p^m$ with $p$ an odd prime and let $M$ be the Fano matroid $F_7$ on seven points: its independent sets are the sets of at most three points other than the seven lines $\{0,1,2\},\{0,3,4\},\{0,5,6\},\{1,3,5\},\{1,4,6\},\{2,3,6\},\{2,4,5\}$. Then
--
--   $$
--   M \text{ is not representable over } \mathrm{GF}(q).
--   $$
--
--   The reason is the classical fact that $F_7$ is representable over a field exactly when the field has characteristic $2$: writing the points in coordinates with respect to three independent ones, the seven line conditions force $2\,sc=0$ for two nonzero coordinates $s,c$, which is impossible in odd characteristic.
--
--   The Fano matroid is one of the excluded minors for ternary representability (the case $q=3$ of Rota's conjecture); this statement records why it is excluded for every odd $q$.
--
--   **Formalization Note** $F_7$ is given by its independent sets on `Fin 7`; representability is the mission's `IsGFRepresentable p m`.
--
--   **Why this is a variation.** This varies Rota's conjecture on excluded minors of the matroids representable over $\mathrm{GF}(q)$. It is a key case: the Fano matroid $F_7$ is representable over a field only in characteristic 2, so it is not $\mathrm{GF}(q)$-representable for any odd prime power $q$, which makes it an excluded minor for those fields. It supplies one of the explicit obstructions that the parent's finite list of excluded minors must contain.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Standard fact that the Fano matroid F_7 is F-representable if and only if the characteristic of F is 2: J. Oxley, Matroid Theory, 2nd ed., Oxford University Press, 2011, Chapter 6 (Representable matroids; proposition number not verified). Excluded minors for GF(3): R. E. Bixby, On Reid's characterization of the ternary matroids, J. Combin. Theory Ser. B 26 (1979), 174–204, and P. D. Seymour, Matroid representation over GF(3), J. Combin. Theory Ser. B 26 (1979), 159–173. Parent problem: TenChallenges.challenge_02 (Rota's conjecture).

import Mathlib
import Definitions.Def_TenChallenges_MatroidRepresentability

namespace LefebvreVariations

/-- Rota's conjecture (Challenge 02), the Fano matroid `F₇`, an excluded minor for
`GF(3)` (Bixby, Seymour; `challenge_02_r3_B4`) and for every `GF(q)`, `q` odd: `F₇` (the
rank-3 matroid on `Fin 7` whose dependent triples are the seven lines
`012, 034, 056, 135, 146, 236, 245` of the Fano plane) is `GF(q)`-representable only in
characteristic `2`. Proof idea: three non-collinear points give a basis, the three lines
through one of them force the remaining coordinates `±1`, and the last line gives
`1 + 1 = 0`.
Source: Oxley, *Matroid Theory*, 2nd ed., Oxford University Press 2011, Proposition 6.4.8
(`F₇` is `F`-representable iff `char F = 2`; section numbering from memory, not verified).
The matroid is given by its independent sets, as in `ch2_unif_two_not_gf_representable`. -/
theorem fano_not_gf_representable_of_odd (p m : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hm : 0 < m)
    (M : Matroid (Fin 7))
    (hI : ∀ I : Set (Fin 7), M.Indep I ↔
      I.encard ≤ 3 ∧ I ≠ {0, 1, 2} ∧ I ≠ {0, 3, 4} ∧ I ≠ {0, 5, 6} ∧ I ≠ {1, 3, 5} ∧
        I ≠ {1, 4, 6} ∧ I ≠ {2, 3, 6} ∧ I ≠ {2, 4, 5}) :
    ¬ IsGFRepresentable p m M := by
  sorry

end LefebvreVariations
