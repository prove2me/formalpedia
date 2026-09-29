-- Prove2me | Theorems.Thm_Module_subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal
-- name    : Module.subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/3ce00dea-b7da-516c-8272-cca04dd02f52
-- title:
--   Length of Ext^g(N,R) over a regular local ring
-- statement:
--   Let $R$ be a commutative Noetherian local ring and let $rs = [x_1,\dots,x_g]$ be a list of elements of $R$ which is weakly regular in the sense of `RingTheory.Sequence.IsWeaklyRegular R rs` (each $x_j$ acts as a regular element on $R/(x_1,\dots,x_{j-1})$) and whose generated ideal `Ideal.ofList rs` is exactly the maximal ideal $\mathfrak m$ of $R$; thus $rs$ is a regular system of parameters and $R$ is regular of dimension $g =$ `rs.length`. Let $N$ be a finitely generated $R$-module, in the same universe as $R$, for which there exists $k \in \mathbb{N}$ such that every $a \in \mathfrak m^k$ annihilates every element of $N$. Then, writing $\mathrm{Ext}^i$ for the derived-category $\mathrm{Ext}$ groups `CategoryTheory.Abelian.Ext` in `ModuleCat R` with their natural $R$-module structure: first, $\mathrm{Ext}^i(N,R)$ is subsingleton, i.e. vanishes, for every $i \neq g$; and second, the `Module.length` of $\mathrm{Ext}^g(N,R)$ over $R$ equals the `Module.length` of $N$ over $R$, as elements of $\mathbb{N}_\infty$.
--
--   This is the $\mathrm{Ext}$ form of local duality for finite-length modules over a regular local ring: such a module is dual to its top $\mathrm{Ext}$ into $R$, with concentration in degree equal to the dimension and preservation of length. It is used by [`Module.length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact`](thm.html#Module.length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact), where lengths of cokernels are compared with lengths of their duals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem Module.subsingleton_ext_and_length_ext_eq_length_of_isWeaklyRegular_of_ofList_eq_maximalIdeal
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R rs)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (htors : ∃ k : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal R ^ k, ∀ z : N, a • z = 0) :
    (∀ i : ℕ, i ≠ rs.length → Subsingleton (Abelian.Ext (ModuleCat.of R N) (ModuleCat.of R R) i)) ∧
      Module.length R (Abelian.Ext (ModuleCat.of R N) (ModuleCat.of R R) rs.length) = Module.length R N := by sorry
