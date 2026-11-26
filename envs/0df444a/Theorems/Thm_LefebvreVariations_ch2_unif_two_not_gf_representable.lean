-- Prove2me | Theorems.Thm_LefebvreVariations_ch2_unif_two_not_gf_representable
-- name    : LefebvreVariations.ch2_unif_two_not_gf_representable
-- status  : Proved
-- author  : @Secousses
-- created : 2026-11-24T21:52:21.0566+00:00
-- url     : https://prove2.me/theorems/1eaec181-96f4-4717-83e2-ad9b0636f1fa
-- title:
--   Lefebvre's variations, No. 1 — on a theme by Rota: $U_{2,q+2}$ is not $\mathrm{GF}(q)$-representable
-- statement:
--   This is the line case of the excluded-minor problem for representability over a finite field (Ten Challenges 02, Rota's conjecture).
--
--   Let $q=p^m$ be a prime power and let $M$ be a matroid on a ground set $E$ with $|E|=q+2$ whose independent sets are exactly the subsets of $E$ with at most two elements, that is, $M$ is the uniform matroid $U_{2,q+2}$. Then
--
--   $$
--   M \text{ is not representable over } \mathrm{GF}(q).
--   $$
--
--   The reason is that a representation would place $q+2$ pairwise non-parallel vectors in a $2$-dimensional subspace over $\mathrm{GF}(q)$, which has only $q+1$ one-dimensional subspaces. Together with the representability of $U_{2,q+1}$, this shows that $U_{2,q+2}$ is an excluded minor for $\mathrm{GF}(q)$-representability, one of the members of every excluded-minor list addressed by Rota's conjecture; for $q=2$ it is Tutte's excluded minor $U_{2,4}$ for binary matroids.
--
--   **Formalization Note** Mathlib has no uniform matroid, so $U_{2,q+2}$ is given by its ground-set size (`encard`) and its independent sets. Representability is the mission's `IsGFRepresentable p m`, a map into a vector space over `GaloisField p m` whose linearly independent subfamilies are exactly the independent sets.
--
--   **Why this is a variation.** This varies Rota's conjecture, that for each finite field $\mathrm{GF}(q)$ the matroids representable over it have only finitely many excluded minors. It is a building block rather than a special case: a rank-2 matroid in which every set of at most two elements is independent (the uniform matroid $U_{2,q+2}$) is not $\mathrm{GF}(q)$-representable, since the projective line over $\mathrm{GF}(q)$ has only $q+1$ points. It exhibits one of the explicit obstructions that the parent's list of excluded minors must contain.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Standard fact that the rank-2 uniform matroid U_{2,n} is GF(q)-representable if and only if n ≤ q+1 (GF(q)^2 has exactly q+1 one-dimensional subspaces): J. Oxley, Matroid Theory, 2nd ed., Oxford University Press, 2011, Chapter 6 (Representable matroids). Case q = 2: W. T. Tutte, A homotopy theorem for matroids, I, II, Trans. Amer. Math. Soc. 88 (1958), 144–174 (U_{2,4} is an excluded minor for binary matroids). Parent problem: TenChallenges.challenge_02 (Rota's conjecture: G.-C. Rota, Combinatorial theory, old and new, Actes Congrès Int. Math. Nice 1970, vol. 3, 229–233).

import Mathlib
import Definitions.Def_TenChallenges_MatroidRepresentability

namespace LefebvreVariations

/-- Rota's conjecture (Challenge 02), a building block: a rank-2 matroid in which
every set of at most two elements is independent (the uniform matroid `U_{2,n}`)
on `q + 2` elements, `q = p ^ m`, is not `GF(q)`-representable, because `GF(q)^2`
has only `q + 1` points of its projective line (Oxley, *Matroid Theory*, 2nd ed.,
Section 6.5; for `q = 2` this is Tutte's excluded minor `U_{2,4}` for binary
matroids). Mathlib has no `unif`, so `U_{2,q+2}` is given by its independent sets. -/
theorem ch2_unif_two_not_gf_representable (p m : ℕ) [Fact p.Prime] (hm : 0 < m)
    {α : Type*} (M : Matroid α)
    (hE : M.E.encard = ((p ^ m + 2 : ℕ) : ℕ∞))
    (hI : ∀ I : Set α, M.Indep I ↔ I ⊆ M.E ∧ I.encard ≤ 2) :
    ¬ IsGFRepresentable p m M := by
  sorry

end LefebvreVariations
