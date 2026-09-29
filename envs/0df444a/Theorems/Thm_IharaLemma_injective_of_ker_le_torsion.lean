-- Prove2me | Theorems.Thm_IharaLemma_injective_of_ker_le_torsion
-- name    : IharaLemma.injective_of_ker_le_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/e0dbb557-4be2-5adb-9c39-02129e0c4cc0
-- title:
--   Injectivity of a localised map with S-torsion kernel
-- statement:
--   Let $R$ be a commutative ring and $S \subseteq R$ a submonoid, and let $V, W, V', W'$ be $R$-modules. Suppose given $R$-linear maps $g : V \to V'$ and $h : W \to W'$ each exhibiting its target as a localisation of its source at $S$ (in Mathlib's sense, `IsLocalizedModule S g` and `IsLocalizedModule S h`), together with $R$-linear maps $f : V \to W$ and $F : V' \to W'$ such that $F(g(v)) = h(f(v))$ for every $v \in V$, i.e. $F$ lies over $f$ along the localisation maps. Suppose further that there is an $R$-submodule $E \le V$ with the two properties: every $e \in E$ is annihilated by some element of $S$, that is, there exists $s \in S$ with $s \cdot e = 0$; and $E$ contains the kernel of $f$, in the sense that $f(v) = 0$ implies $v \in E$. The conclusion is that $F$ is injective as a function $V' \to W'$.
--
--   This is the standard localisation step in arguments of Ihara type: a map between localised modules is injective as soon as the kernel of the unlocalised map is $S$-torsion. It is used in the construction of the auxiliary-level comparison isomorphism [`CuspForm.AuxLevel.exists_linearEquiv_baseML_prod_ML`](thm.html#CuspForm.AuxLevel.exists_linearEquiv_baseML_prod_ML).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaLemma_injective_of_ker_le_torsion.lean

import Mathlib.Algebra.Module.LocalizedModule.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IharaLemma.injective_of_ker_le_torsion {R : Type*} [CommRing R] (S : Submonoid R)
    {V W V' W' : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']
    (g : V →ₗ[R] V') [IsLocalizedModule S g] (h : W →ₗ[R] W') [IsLocalizedModule S h]
    (f : V →ₗ[R] W) (F : V' →ₗ[R] W') (hcomm : ∀ v, F (g v) = h (f v))
    (E : Submodule R V) (hE : ∀ e ∈ E, ∃ s : S, (s : R) • e = 0) (hker : ∀ v, f v = 0 → v ∈ E) :
    Function.Injective F := by sorry
