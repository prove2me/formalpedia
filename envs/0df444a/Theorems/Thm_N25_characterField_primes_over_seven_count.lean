-- Prove2me | Theorems.Thm_N25_characterField_primes_over_seven_count
-- name    : N25.characterField_primes_over_seven_count
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:51.478637+00:00
-- url     : https://prove2.me/theorems/116f8381-b872-408a-916a-37a9eafbda4f
-- title:
--   At most five primes lie above $7$
-- statement:
--   Let $K$ be the quintic character field. The set of prime ideals of $\mathcal O_K$ lying above the ideal $(7)\subseteq\mathbb Z$ has cardinality at most five:
--
--   $$\bigl|\{P\subseteq\mathcal O_K:P\text{ prime and }P\mid(7)\}\bigr|\le 5.$$
--
--   Together with uniqueness above $5$, this gives the required seven-element norm cover.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CharacterField
import Definitions.Def_N25
import Mathlib.NumberTheory.RamificationInertia.Galois

set_option autoImplicit false
open scoped NumberField
open N25

theorem N25.characterField_primes_over_seven_count :
    (Ideal.primesOver (Ideal.span {(7 : ℤ)}) (𝓞 characterField)).ncard ≤ 5 := by sorry
