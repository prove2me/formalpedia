-- Prove2me | Theorems.Thm_HScattered_LinearSets_proposition_4_2_2
-- name    : HScattered.LinearSets.proposition_4_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:00.848033+00:00
-- url     : https://prove2.me/theorems/fac1e077-43cb-4dcd-83a5-b23774f20ccb
-- title:
--   Proposition 4.2 (2) — meeting subspaces defining the same linear set of size q + 1 coincide
-- statement:
--   Let $V$ be a two-dimensional vector space over $\mathbb F_{q^n}$ and let $U$, $W$ be $\mathbb F_q$-subspaces of $V$ that define the same linear set of $\mathrm{PG}(1,q^n)$, of size $q+1$. If $U$ and $W$ have a nonzero vector in common, then they are equal:
--
--   $$
--   L_U = L_W,\quad |L_U| = q+1,\quad U\cap W \ne \{0\} \quad\Longrightarrow\quad U = W .
--   $$
--
--   This result is quoted in the paper from Bonoli and Polverino [5, p. 3, Eq. (6) and Lemma 2.1]. It is the rigidity step in the proof of Lemma 4.4.
--
--   **Formalization Note** The size condition is `Set.ncard (linearSet F K U) = Fintype.card F + 1`, and $U\cap W\ne\{0\}$ is `U ⊓ W ≠ ⊥`.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 13, Proposition 4.2 part 2 (citing [5, p. 3 Eq. (6) and Lemma 2.1])

import Mathlib
import Definitions.Def_HScattered_LinearSets_LinearSet

namespace HScattered.LinearSets

/-- Proposition 4.2, part 2 (arXiv:1906.10590v2, p. 13; from [5]). Let `V` be a
two-dimensional vector space over `𝔽_{qⁿ}`, and let `U`, `W` be `𝔽_q`-subspaces of `V` with
`L_U = L_W` of size `q + 1`. If `U ∩ W ≠ {0}`, then `U = W`. -/
theorem proposition_4_2_2 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K]
    (hV : Module.finrank K V = 2) (U W : Submodule F V)
    (hUW : linearSet F K U = linearSet F K W)
    (hL : (linearSet F K U).ncard = Fintype.card F + 1)
    (hint : U ⊓ W ≠ ⊥) :
    U = W := by sorry

end HScattered.LinearSets
