-- Prove2me | Theorems.Thm_Module_faithfullyFlat_pi_of_forall_faithfullyFlat
-- name    : Module.faithfullyFlat_pi_of_forall_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/3493a811-507e-5bbd-95e8-342d884c7016
-- title:
--   Faithful flatness of a finite product of algebras
-- statement:
--   Let $k$ be a natural number and let $C, D : \mathrm{Fin}\,k \to \mathrm{Type}$ be two families of types, each $C_i$ and each $D_i$ carrying a commutative ring structure, and each $D_i$ carrying an algebra structure over $C_i$. Suppose moreover that the product ring $\prod_i D_i$ is equipped with an algebra structure `inst` over the product ring $\prod_i C_i$, and assume the compatibility hypothesis `halg`: for every index $i$ and every $x \in \prod_i C_i$, the $i$-th component of $\mathrm{algebraMap}_{\prod C,\ \prod D}(x)$ equals $\mathrm{algebraMap}_{C_i, D_i}(x_i)$, i.e. the structure map of `inst` is the product of the given component structure maps. Assume finally that for each $i$ the $C_i$-module $D_i$ is faithfully flat. The conclusion is that $\prod_i D_i$ is faithfully flat as a module over $\prod_i C_i$, for the module structure underlying `inst`.
--
--   This is the standard fact that faithful flatness of a finite family of algebras $C_i \to D_i$ passes to the induced algebra $\prod_i C_i \to \prod_i D_i$, stated here for a product algebra structure characterised axiomatically by its componentwise behaviour rather than fixed to be `Pi.algebra`. It is used in the construction of a faithfully flat extension splitting off a principal square root of a polarisation, via [`AlgebraicGeometry.Polarisation.exists_faithfullyFlat_principalSqrt_of_forall_pullback_of_isPullback_pi`](thm.html#AlgebraicGeometry.Polarisation.exists_faithfullyFlat_principalSqrt_of_forall_pullback_of_isPullback_pi).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_faithfullyFlat_pi_of_forall_faithfullyFlat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.faithfullyFlat_pi_of_forall_faithfullyFlat
    {k : ℕ} (C : Fin k → Type) [∀ i, CommRing (C i)] (D : Fin k → Type) [∀ i, CommRing (D i)] [∀ i, Algebra (C i) (D i)]
    [inst : Algebra (∀ i, C i) (∀ i, D i)]
    (halg : ∀ (i : Fin k) (x : ∀ i, C i), algebraMap (∀ i, C i) (∀ i, D i) x i = algebraMap (C i) (D i) (x i))
    (hff : ∀ i, Module.FaithfullyFlat (C i) (D i)) :
    @Module.FaithfullyFlat (∀ i, C i) (∀ i, D i) _ _ inst.toModule := by sorry
