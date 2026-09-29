-- Prove2me | Theorems.Thm_IsNoetherianRing_exists_completeOrthogonalIdempotents_forall_mul_eq_zero_or_eq
-- name    : IsNoetherianRing.exists_completeOrthogonalIdempotents_forall_mul_eq_zero_or_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/be9ed435-a124-5acd-b377-b0489fdd2c55
-- title:
--   Noetherian rings: complete families of primitive idempotents
-- statement:
--   Let $B$ be a commutative ring in a fixed universe which is Noetherian. The assertion is that there exist a natural number $n$ and a family $e : \mathrm{Fin}\,n \to B$ such that `CompleteOrthogonalIdempotents e` holds, i.e. each $e_i$ is idempotent, $e_i e_j = 0$ whenever $i \neq j$, and $\sum_{i} e_i = 1$; and moreover, for every index $i$, first $e_i \neq 0$, and second, for every $x \in B$ with $x^2 = x$ one has $x e_i = 0$ or $x e_i = e_i$. The second clause is the primitivity of $e_i$ in a strong, "local" form: it says not merely that $e_i$ admits no splitting into two nonzero orthogonal idempotents, but that every idempotent of $B$ restricts on the factor $Be_i$ to $0$ or to its identity, so each $Be_i$ has no idempotents other than $0$ and $1$. No nontriviality of $B$ is assumed; for the zero ring the empty family ($n = 0$) is produced.
--
--   This is the decomposition of a commutative Noetherian ring into finitely many factors with connected spectrum, recorded as a complete family of pairwise orthogonal nonzero primitive idempotents summing to $1$. It is used in the construction of fine moduli for rigidified quaternionic curves in the Čerednik–Drinfeld part of the development, where statements over a Noetherian base are reduced to the factors on which all idempotents are trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsNoetherianRing_exists_completeOrthogonalIdempotents_forall_mul_eq_zero_or_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem IsNoetherianRing.exists_completeOrthogonalIdempotents_forall_mul_eq_zero_or_eq
    (B : Type u) [CommRing B] [IsNoetherianRing B] :
    ∃ (n : ℕ) (e : Fin n → B), CompleteOrthogonalIdempotents e ∧
      ∀ i : Fin n, e i ≠ 0 ∧ ∀ x : B, IsIdempotentElem x → x * e i = 0 ∨ x * e i = e i := by sorry
