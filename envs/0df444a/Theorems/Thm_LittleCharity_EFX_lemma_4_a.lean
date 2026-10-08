-- Prove2me | Theorems.Thm_LittleCharity_EFX_lemma_4_a
-- name    : LittleCharity.EFX.lemma_4_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:27.570344+00:00
-- url     : https://prove2.me/theorems/bf2231b0-4bf5-4ba2-8abd-306a29fb8ff9
-- title:
--   Lemma 4(a) — Rule U0 preserves EFX and shrinks the pool
-- statement:
--   Let $X$ be an allocation under monotone valuations, let $g\in P(X)$ be a pool good and $i$ an agent such that giving $g$ to $i$ produces an EFX allocation $X'$ (Rule $U_0$: $X'_i=X_i\cup\{g\}$, $X'_j=X_j$ for $j\ne i$). Then
--   $$
--   X'\text{ is an EFX allocation},\qquad \phi(X')\ge\phi(X),\qquad |P(X')|+1=|P(X)|.
--   $$
--   So an application of $U_0$ never lowers social welfare and shrinks the pool by exactly one good.
--
--   **Formalization Note** "Rule $U_0$ returns an EFX allocation" is the rule's precondition, which the Lean statement takes as a hypothesis and repeats in the conclusion, as the page's proof says ("follows directly from the precondition"). The pool decrease is written $|P(X')|+1=|P(X)|$ to avoid truncated natural-number subtraction.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, pp. 9–10, Algorithm 2 Rule U0 and Lemma 4(a)

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting

namespace LittleCharity.EFX

theorem lemma_4_a {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hmono : IsMonotoneVal v) (X : Fin n → Finset (Fin m))
    (hX : IsPartialAllocation X) (g : Fin m) (hg : g ∈ pool X) (i : Fin n)
    (hEFX' : IsEFX v (Function.update X i (insert g (X i)))) :
    let X' := Function.update X i (insert g (X i))
    IsPartialAllocation X' ∧ IsEFX v X' ∧
    welfare v X ≤ welfare v X' ∧
    (pool X').card + 1 = (pool X).card := by sorry
end LittleCharity.EFX
