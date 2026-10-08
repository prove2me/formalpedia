-- Prove2me | Theorems.Thm_HScattered_LinearSets_lemma_4_4
-- name    : HScattered.LinearSets.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:53.68197+00:00
-- url     : https://prove2.me/theorems/2e755460-b9a6-4b15-bf18-ded315a16045
-- title:
--   Lemma 4.4 — a linear set scattered with respect to lines determines its subspace up to a nonzero scalar
-- statement:
--   Let $V = V(r,q^n)$ and let $U$ be a $2$-scattered $\mathbb F_q$-subspace of $V$, so that $L_U$ is scattered with respect to lines in $\mathrm{PG}(r-1,q^n)$. If $W$ is any $\mathbb F_q$-subspace of $V$ with $L_U = L_W$, then there is a nonzero scalar $\lambda\in\mathbb F_{q^n}^*$ with
--
--   $$
--   U = \lambda W = \{\lambda w : w \in W\}.
--   $$
--
--   The converse is immediate, since $L_{\lambda W} = L_W$. Combined with Proposition 2.1, the lemma reduces the equivalence question of Theorem 4.5 for $h \ge 2$ to the orbits of $\Gamma\mathrm L(r,q^n)$.
--
--   **Formalization Note** The conclusion is `∃ c : K, c ≠ 0 ∧ (U : Set V) = (c • ·) '' W`. $W$ is not assumed to be scattered.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 13, Lemma 4.4

import Mathlib
import Definitions.Def_HScattered_Bound_IsHScattered
import Definitions.Def_HScattered_LinearSets_LinearSet

namespace HScattered.LinearSets

/-- Lemma 4.4 (arXiv:1906.10590v2, p. 13). Let `L_U` be scattered with respect to lines in
`PG(r − 1, qⁿ)` (`U` is 2-scattered). If `L_U = L_W` for some `𝔽_q`-subspace `W`, then
`U = λW` for some `λ ∈ 𝔽_{qⁿ}^*`. -/
theorem lemma_4_4 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (U : Submodule F V) (hU : HScattered.Bound.IsHScattered F K 2 U)
    (W : Submodule F V) (hW : linearSet F K U = linearSet F K W) :
    ∃ c : K, c ≠ 0 ∧ (U : Set V) = (fun w : V => c • w) '' (W : Set V) := by sorry

end HScattered.LinearSets
