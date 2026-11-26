-- Prove2me | Theorems.Thm_LefebvreVariations_unif_two_gf_representable
-- name    : LefebvreVariations.unif_two_gf_representable
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:37:51.415898+00:00
-- url     : https://prove2.me/theorems/7aa2834d-7c58-4900-9962-d0bccdc80957
-- title:
--   Lefebvre's variations, No. 27 — on a theme by Rota: $U_{2,n}$ is $\mathrm{GF}(q)$-representable for $n\le q+1$
-- statement:
--   This is the positive half of the line case of Rota's conjecture.
--
--   Let $q=p^m$ be a prime power and let $M$ be a matroid on a ground set $E$ with $|E|\le q+1$ whose independent sets are exactly the subsets of $E$ with at most two elements, that is, $M\cong U_{2,|E|}$. Then
--
--   $$
--   M \text{ is representable over } \mathrm{GF}(q).
--   $$
--
--   A representation places the elements of $E$ at distinct points of the projective line over $\mathrm{GF}(q)$, which has exactly $q+1$ points: any two of the chosen vectors are linearly independent and any three are dependent. Together with the non-representability of $U_{2,q+2}$ (Lefebvre's variations, No. 3), this gives the sharp statement that $U_{2,n}$ is $\mathrm{GF}(q)$-representable if and only if $n\le q+1$, and shows that every proper minor of the line $U_{2,q+2}$ is representable, the first step in recognizing it as an excluded minor in Rota's conjecture.
--
--   **Formalization Note** $U_{2,n}$ is given by its ground-set size (`encard`) and its independent sets; representability is the mission's `IsGFRepresentable p m`.
--
--   **Why this is a variation.** This varies Rota's conjecture on excluded minors of matroids representable over a finite field (`TenChallenges.challenge_02`). It is a special case: the rank-$2$ uniform matroid $U_{2,n}$ is $\mathrm{GF}(q)$-representable exactly when $n\le q+1$, and this is the positive half, for $n\le q+1$. Together with the non-representability of $U_{2,q+2}$ it shows every proper minor of $U_{2,q+2}$ is representable, the first step toward recognizing it as an excluded minor in the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Standard fact that the rank-2 uniform matroid U_{2,n} is GF(q)-representable if and only if n ≤ q+1 (the projective line PG(1,q) has q+1 points): J. Oxley, Matroid Theory, 2nd ed., Oxford University Press, 2011, Chapter 6 (Representable matroids). Parent problem: TenChallenges.challenge_02 (Rota's conjecture: G.-C. Rota, Combinatorial theory, old and new, Actes Congrès Int. Math. Nice 1970, vol. 3, 229–233).

import Mathlib
import Definitions.Def_TenChallenges_MatroidRepresentability

namespace LefebvreVariations

/-- Rota's conjecture (Challenge 02), the sharp positive half of the `U_{2,q+2}` block:
a rank-2 matroid in which every set of at most two elements is independent (the uniform
matroid `U_{2,n}`) on `n ≤ q + 1` elements, `q = p ^ m`, IS `GF(q)`-representable: its
elements are sent to distinct points of the projective line `PG(1,q)`, which has
exactly `q + 1` points. Together with the `n = q + 2` obstruction this gives
"`U_{2,n}` is `GF(q)`-representable iff `n ≤ q + 1`", and shows that `U_{2,q+2}` has
only representable proper minors, the first step to making it an excluded minor.
Source: Oxley, *Matroid Theory*, 2nd ed., Oxford University Press 2011, Section 6.5
(uniform matroids over finite fields; for `q = 2`, Tutte's `U_{2,3}` binary and
`U_{2,4}` the excluded minor, Tutte 1958, Trans. Amer. Math. Soc. 88, 144-174).
Mathlib has no `unif`, so `U_{2,n}` is given by its independent sets. -/
theorem unif_two_gf_representable (p m : ℕ) [Fact p.Prime] (hm : 0 < m)
    {α : Type*} (M : Matroid α)
    (hE : M.E.encard ≤ ((p ^ m + 1 : ℕ) : ℕ∞))
    (hI : ∀ I : Set α, M.Indep I ↔ I ⊆ M.E ∧ I.encard ≤ 2) :
    IsGFRepresentable p m M := by
  sorry

end LefebvreVariations
