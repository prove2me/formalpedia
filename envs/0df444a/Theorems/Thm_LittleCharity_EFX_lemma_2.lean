-- Prove2me | Theorems.Thm_LittleCharity_EFX_lemma_2
-- name    : LittleCharity.EFX.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:41:22.615535+00:00
-- url     : https://prove2.me/theorems/a93d0476-a6b4-496b-87ea-d5908bad41a3
-- title:
--   Lemma 2 — eliminating an envy cycle preserves EFX and raises welfare
-- statement:
--   Let $X$ be an allocation and let $i_0\to i_1\to\cdots\to i_{k-1}\to i_0$ be a cycle of distinct agents in the envy graph $G_X$, i.e. $v_{i_\ell}(X_{i_\ell})<v_{i_\ell}(X_{i_{\ell+1}})$ for every $\ell$ (indices modulo $k$). Let $X'$ be the allocation with $X'_{i_\ell}=X_{i_{\ell+1}}$ for $\ell\in\{0,\dots,k-1\}$ and $X'_j=X_j$ for agents $j$ off the cycle. Then
--
--   1. $X'$ is again an allocation (pairwise disjoint bundles) with the same pool, $P(X')=P(X)$;
--   2. if $X$ is EFX, then $X'$ is EFX;
--   3. the social welfare strictly increases:
--   $$
--   \phi(X')>\phi(X).
--   $$
--
--   This decycling step lets the algorithm keep the envy graph acyclic while preserving EFX and making strict progress in welfare.
--
--   **Formalization Note** The cycle is a nonempty duplicate-free list $c$ of agents, and the edge condition says each agent of $c$ envies her successor under Mathlib's cyclic permutation `List.formPerm c`; then $X'=X\circ$`formPerm`$\,c$. Item 1 is the well-formedness Algorithm 1 relies on and is added to the page's statement; it needs the input to be an allocation, which the page presupposes.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, p. 8, Lemma 2

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting

namespace LittleCharity.EFX

theorem lemma_2 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X)
    (c : List (Fin n)) (hc : c.Nodup) (hne : c ≠ [])
    (hcycle : ∀ a ∈ c, Envies v X a (c.formPerm a)) :
    IsPartialAllocation (X ∘ c.formPerm) ∧
    pool (X ∘ c.formPerm) = pool X ∧
    (IsEFX v X → IsEFX v (X ∘ c.formPerm)) ∧
    welfare v X < welfare v (X ∘ c.formPerm) := by sorry
end LittleCharity.EFX
