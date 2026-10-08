-- Prove2me | Theorems.Thm_HScattered_LinearSets_proposition_4_2_1
-- name    : HScattered.LinearSets.proposition_4_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:55.981185+00:00
-- url     : https://prove2.me/theorems/9b4a9604-cf7c-4f66-84b6-dc5fab858815
-- title:
--   Proposition 4.2 (1) — a linear set of size q + 1 in PG(1, qⁿ) has rank 2
-- statement:
--   Let $V$ be a two-dimensional vector space over $\mathbb F_{q^n}$, so that $\mathrm{PG}(V,\mathbb F_{q^n}) = \mathrm{PG}(1,q^n)$ is a projective line. If $U$ is an $\mathbb F_q$-subspace of $V$ whose linear set has exactly $q+1$ points, then
--
--   $$
--   |L_U| = q+1 \quad\Longrightarrow\quad \dim_{\mathbb F_q} U = 2 .
--   $$
--
--   This result is quoted in the paper from Bonoli and Polverino [5, p. 3, Eq. (6) and Lemma 2.1]. It is the tool that bounds the dimension of the intersection of a scattered subspace with the $\mathbb F_{q^n}$-span of two vectors in the proofs of Proposition 4.3 and Lemma 4.4.
--
--   **Formalization Note** $|L_U|$ counts points, i.e. one-dimensional $\mathbb F_{q^n}$-subspaces, as `Set.ncard (linearSet F K U)`; $q$ is `Fintype.card F`.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 13, Proposition 4.2 part 1 (citing [5, p. 3 Eq. (6) and Lemma 2.1])

import Mathlib
import Definitions.Def_HScattered_LinearSets_LinearSet

namespace HScattered.LinearSets

/-- Proposition 4.2, part 1 (arXiv:1906.10590v2, p. 13; from [5]). Let `V` be a
two-dimensional vector space over `𝔽_{qⁿ}`. If `U` is an `𝔽_q`-subspace of `V` whose linear set
`L_U` has exactly `q + 1` points, then `dim_{𝔽_q} U = 2`. -/
theorem proposition_4_2_1 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K]
    (hV : Module.finrank K V = 2) (U : Submodule F V)
    (hL : (linearSet F K U).ncard = Fintype.card F + 1) :
    Module.finrank F U = 2 := by sorry

end HScattered.LinearSets
