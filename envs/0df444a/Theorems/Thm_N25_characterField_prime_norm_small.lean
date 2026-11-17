-- Prove2me | Theorems.Thm_N25_characterField_prime_norm_small
-- name    : N25.characterField_prime_norm_small
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:39.935209+00:00
-- url     : https://prove2.me/theorems/2139dc48-3efb-4cc7-8a84-14029524ef27
-- title:
--   A nonzero prime of norm at most $24$ has norm $5$ or $7$
-- statement:
--   Let $K$ be the quintic character field and let $P\ne 0$ be a prime ideal of $\mathcal O_K$. If its absolute norm is at most $24$, then
--
--   $$N(P)=5\quad\text{or}\quad N(P)=7.$$
--
--   This reduces the enumeration of small prime ideals to the primes above $5$ and $7$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CharacterField
import Definitions.Def_N25
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Basic

set_option autoImplicit false
open scoped NumberField
open N25

theorem N25.characterField_prime_norm_small (P : Ideal (𝓞 characterField))
    [P.IsPrime] (hP : P ≠ ⊥) (hbound : P.absNorm ≤ 24) :
    P.absNorm = 5 ∨ P.absNorm = 7 := by sorry
