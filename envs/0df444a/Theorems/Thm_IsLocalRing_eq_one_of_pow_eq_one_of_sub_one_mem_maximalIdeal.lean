-- Prove2me | Theorems.Thm_IsLocalRing_eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal
-- name    : IsLocalRing.eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/a8865be1-36bb-55c6-a542-3b9c0b296e33
-- title:
--   Principal units have no n-torsion when n is invertible
-- statement:
--   Let $A$ be a commutative ring that is local, with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal A`. Let $u \in A$ satisfy $u - 1 \in \mathfrak m$, i.e. $u$ is a principal unit, congruent to $1$ modulo the maximal ideal. Let $n$ be a natural number whose image $(n : A)$ under the canonical ring map $\mathbb{N} \to A$ is a unit of $A$, and suppose $u^n = 1$. Then $u = 1$. No completeness, Noetherian or Henselian hypothesis is imposed, and no assumption is made on the residue characteristic beyond what the invertibility of $(n : A)$ entails; note that $u$ is not assumed a priori to be a unit (it is one, being congruent to $1$ modulo $\mathfrak m$), and the case $n = 0$ is excluded automatically since then $(0 : A)$ would have to be a unit.
--
--   This is the statement that the group $1 + \mathfrak m$ of principal units of a local ring contains no nontrivial $n$-torsion when $n$ is invertible in $A$; for a complete local ring of residue characteristic $p$ it expresses that $1 + \mathfrak m$ is torsion-free away from $p$. It is used by [`MonoidHom.apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one`](thm.html#MonoidHom.apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one) to kill prime-to-$p$ characters valued in $1 + \mathfrak m$, the mechanism behind tame descent in the minimal deformation conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing

theorem IsLocalRing.eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal {A : Type u} [CommRing A] [IsLocalRing A]
    {u : A} (hu : u - 1 ∈ IsLocalRing.maximalIdeal A) {n : ℕ} (hn : IsUnit (n : A)) (hun : u ^ n = 1) : u = 1 := by sorry
