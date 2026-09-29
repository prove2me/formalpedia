-- Prove2me | Theorems.Thm_Ideal_exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le
-- name    : Ideal.exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/3677d6df-2d4d-5ad1-85a5-af5a2550c005
-- title:
--   Idempotent ideal in a Noetherian ring is annihilated off a prime
-- statement:
--   Let $B$ be a commutative ring that is Noetherian, let $I$ be an ideal of $B$ satisfying $I \le I^2$ (every element of $I$ lies in the square of $I$), and let $P$ be a prime ideal of $B$ with $I \le P$. The conclusion asserts the existence of an element $f \in B$ such that $f \notin P$ and $f \cdot a = 0$ for every $a \in I$. Thus a single element of $B$ outside $P$ annihilates $I$ elementwise; equivalently, $I$ becomes the zero ideal in the localisation $B_f$, hence also in $B_P$. No hypothesis of local-ness or of finiteness beyond Noetherianity of $B$ is imposed, and the primality of $P$ enters only through $1 \notin P$ together with closure of $P$ under subtraction.
--
--   This is the standard Nakayama-type consequence of an idempotent finitely generated ideal: such an ideal is annihilated by an element congruent to $1$ modulo itself, so its zero locus contains an open neighbourhood of any prime containing it. It is used in the Čerednik–Drinfel'd part of the development, in the two statements about rigidified special formal modules which produce a scalar matching a map on $n$-torsion from divided-power or Verschiebung/Teichmüller relations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ideal.exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le
    {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal B) (hI : I ≤ I ^ 2)
    (P : Ideal B) [P.IsPrime] (hIP : I ≤ P) :
    ∃ f : B, f ∉ P ∧ ∀ a ∈ I, f * a = 0 := by sorry
