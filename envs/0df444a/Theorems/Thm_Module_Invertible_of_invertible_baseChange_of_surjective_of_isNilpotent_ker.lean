-- Prove2me | Theorems.Thm_Module_Invertible_of_invertible_baseChange_of_surjective_of_isNilpotent_ker
-- name    : Module.Invertible.of_invertible_baseChange_of_surjective_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/6ca80e64-a0b0-5547-b67d-67500d38fe30
-- title:
--   Invertibility descends along a nilpotent surjection
-- statement:
--   Let $R$ and $S$ be commutative rings with $S$ an $R$-algebra, and suppose the structure map $R \to S$ is surjective and that its kernel is a nilpotent ideal, i.e. some power of $\ker(R \to S)$ is the zero ideal. Let $P$ be an $R$-module which is finitely generated and projective over $R$. The hypothesis is that the base change $S \otimes_R P$ is an invertible $S$-module in the sense of Mathlib's `Module.Invertible`. The conclusion is that $P$ is itself an invertible $R$-module. The three types $R$, $S$ and $P$ live in unrelated universes.
--
--   This is the descent of invertibility (local freeness of rank one, in the form of Mathlib's `Module.Invertible`) along a nilpotent thickening $\operatorname{Spec} S \hookrightarrow \operatorname{Spec} R$ with $S = R/I$, $I$ nilpotent. It is used in the Cerednik–Drinfeld part of the development, where it supports [`CerednikDrinfeld.FormalODModule.isSpecial_of_isSpecial_map_of_surjective_of_isNilpotent`](thm.html#CerednikDrinfeld.FormalODModule.isSpecial_of_isSpecial_map_of_surjective_of_isNilpotent), transferring a rank-one condition on a formal module from a quotient back to the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Invertible_of_invertible_baseChange_of_surjective_of_isNilpotent_ker.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open TensorProduct

theorem Module.Invertible.of_invertible_baseChange_of_surjective_of_isNilpotent_ker
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hπ : Function.Surjective (algebraMap R S)) (hker : IsNilpotent (RingHom.ker (algebraMap R S)))
    (P : Type w) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    (h : Module.Invertible S (S ⊗[R] P)) : Module.Invertible R P := by sorry
