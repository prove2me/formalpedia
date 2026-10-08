-- Prove2me | Theorems.Thm_LittleCharity_EFX_lemma_5
-- name    : LittleCharity.EFX.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:08.819981+00:00
-- url     : https://prove2.me/theorems/bdc383d4-cf33-4ac6-bfb0-adc7496e6f19
-- title:
--   Lemma 5 — Rule U1 increases welfare and preserves EFX
-- statement:
--   Let $X$ be an EFX allocation under monotone valuations, and suppose some agent $k$ values the pool above her own bundle, $v_k(P)>v_k(X_k)$ (Rule $U_1$'s precondition). Let $Z$ be an inclusion-wise minimal envied subset of $P=P(X)$ and $i$ an agent with $v_i(Z)>v_i(X_i)$. Let $X'$ be obtained by setting $X'_i=Z$ and $X'_j=X_j$ for $j\ne i$. Then $X'$ is an allocation, it is EFX, welfare strictly increases, and the new pool is the one of Algorithm 2, line 8:
--   $$
--   \phi(X')>\phi(X),\qquad P(X')=X_i\cup\bigl(P\setminus Z\bigr).
--   $$
--
--   Rule $U_1$ is thus a strict welfare step whenever the pool itself is envied.
--
--   **Formalization Note** The EFX hypothesis on $X$ is Algorithm 1's invariant. "The most envious agent of $P$" is encoded by taking any minimal envied subset $Z$ of the pool and any agent who envies it, as Definition 3 and line 6 specify.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, p. 10, Algorithm 2 Rule U1 and Lemma 5

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting

namespace LittleCharity.EFX

theorem lemma_5 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hmono : IsMonotoneVal v) (X : Fin n → Finset (Fin m))
    (hX : IsPartialAllocation X) (hEFX : IsEFX v X)
    (hU1 : ∃ k, v k (X k) < v k (pool X))
    (i : Fin n) (Z : Finset (Fin m))
    (hZ : IsMinimalEnviedSubset v X (pool X) Z)
    (hi : v i (X i) < v i Z) :
    let X' := Function.update X i Z
    IsPartialAllocation X' ∧ IsEFX v X' ∧
    welfare v X < welfare v X' ∧
    pool X' = X i ∪ (pool X \ Z) := by sorry
end LittleCharity.EFX
