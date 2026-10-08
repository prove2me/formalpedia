-- Prove2me | Theorems.Thm_HScattered_LinearSets_proposition_2_1
-- name    : HScattered.LinearSets.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:25.705966+00:00
-- url     : https://prove2.me/theorems/48f9e0c3-4a7c-4810-a9f9-54d26636596f
-- title:
--   Proposition 2.1 — h-scattered subspaces are i-scattered for every 0 < i < h
-- statement:
--   Let $V = V(r,q^n)$ be an $r$-dimensional vector space over $\mathbb F_{q^n}$ and let $U$ be an $\mathbb F_q$-subspace of $V$. If $h > 1$ and $U$ is $h$-scattered, then for every integer $i$ with $0 < i < h$,
--
--   $$
--   U \text{ is } i\text{-scattered}.
--   $$
--
--   In particular every $h$-scattered subspace is $1$-scattered (scattered). The proposition shows that $h$-scattered subspaces form subclasses of the scattered ones, and it is how the $2$-scattered hypothesis of Lemma 4.4 is obtained from the $h$-scattered hypothesis of Theorem 4.5, and how Proposition 4.3 obtains $1$-scatteredness.
--
--   **Formalization Note** "For any $i < h$" is read as $0 < i < h$, since Definition 1.1 only defines $i$-scattered for $i > 0$. The fields are finite and $V$ is finite-dimensional.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 3, Proposition 2.1

import Mathlib
import Definitions.Def_HScattered_Bound_IsHScattered

namespace HScattered.LinearSets

/-- Proposition 2.1 (arXiv:1906.10590v2, p. 3). For `h > 1`, an `h`-scattered `𝔽_q`-subspace
of `V(r, qⁿ)` is also `i`-scattered for every `0 < i < h`; in particular it is 1-scattered. -/
theorem proposition_2_1 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h i : ℕ) (U : Submodule F V) (hh : 1 < h) (hU : HScattered.Bound.IsHScattered F K h U)
    (hi0 : 0 < i) (hih : i < h) :
    HScattered.Bound.IsHScattered F K i U := by sorry

end HScattered.LinearSets
