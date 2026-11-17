-- Prove2me | Theorems.Thm_N25_characterField_small_norm_ideal
-- name    : N25.characterField_small_norm_ideal
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:39.812211+00:00
-- url     : https://prove2.me/theorems/6188d930-b9b7-4ec8-809c-e6a947cae309
-- title:
--   Every nonzero ideal of norm at most $24$ is trivial or has norm $5$ or $7$
-- statement:
--   Let $K$ be the quintic character field and let $I$ be a nonzero integral ideal of $\mathcal O_K$. If $N(I)\le 24$, then either $I=\mathcal O_K$, or its absolute norm is $5$, or its absolute norm is $7$:
--
--   $$N(I)\le 24\Longrightarrow I=\mathcal O_K\ \lor\ N(I)=5\ \lor\ N(I)=7.$$
--
--   This classifies all ideals that can occur below the Minkowski norm bound.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CharacterField
import Definitions.Def_N25
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Basic

set_option autoImplicit false
open scoped NumberField nonZeroDivisors
open N25

theorem N25.characterField_small_norm_ideal (I : (Ideal (𝓞 characterField))⁰)
    (hbound : Ideal.absNorm (I : Ideal (𝓞 characterField)) ≤ 24) :
    (I : Ideal (𝓞 characterField)) = ⊤ ∨
    Ideal.absNorm (I : Ideal (𝓞 characterField)) = 5 ∨
    Ideal.absNorm (I : Ideal (𝓞 characterField)) = 7 := by sorry
