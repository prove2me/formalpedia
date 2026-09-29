-- Prove2me | Theorems.Thm_ModularCurve_mazurPrinciple_toric_exclusion_of_scalar
-- name    : ModularCurve.mazurPrinciple_toric_exclusion_of_scalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/8ef17561-d6a6-518a-a539-81aa5f595c85
-- title:
--   Toric exclusion with scalar Frobenius forces q=0 or q=1
-- statement:
--   Let $G$ be a group, $k$ a field and $V$ a $k$-vector space carrying a distributive $G$-action whose operators commute with the scalars, let $R$ be a commutative ring and $J$ an $R$-module carrying a distributive $G$-action, let $q$ be a natural number, $\varphi \in G$, and let $\mathcal{T}$ be an $R$-submodule of $J$. Assume the predicate `ToricFrobeniusSq q φ 𝒯`, which says exactly that $\varphi \cdot \varphi \cdot x = q^{2} x$ (with $q^2$ acting through $\mathbb{Z}$) for every $x \in \mathcal{T}$. Assume given an additive map $\iota : V \to J$ that is injective, is $G$-equivariant in the sense that $\iota(g \cdot v) = g \cdot \iota(v)$ for all $g \in G$ and $v \in V$, and whose values all lie in $\mathcal{T}$. Assume further that there is a scalar $\lambda \in k$ with $\varphi \cdot v = \lambda v$ for every $v \in V$, that $\dim_k V = 2$, and that the $k$-linear endomorphism of $V$ induced by $\varphi$ has determinant $q$ in $k$. The conclusion is that $q = 0$ or $q = 1$ in $k$.
--
--   This is the toric exclusion step in Mazur's principle: on the toric part the Frobenius-square relation together with the determinant normalisation $\det \varphi = q$ leaves no room unless $q \equiv 0$ or $q \equiv 1$ in the residue field. Unlike the form of the statement without the scalar hypothesis, which only yields $q = 0$ or $q^{2} = 1$, the scalar hypothesis here removes the case $q \equiv -1$; the result is used by [`ModularCurve.mazurPrinciple_of_ne_one_of_toricDichotomy`](thm.html#ModularCurve.mazurPrinciple_of_ne_one_of_toricDichotomy).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mazurPrinciple_toric_exclusion_of_scalar.lean

import Mathlib
import Definitions.Def_ModularCurve_DeligneRapoport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.mazurPrinciple_toric_exclusion_of_scalar
    {G : Type*} [Group G]
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [DistribMulAction G V] [SMulCommClass G k V]
    {R : Type*} [CommRing R]
    {J : Type*} [AddCommGroup J] [Module R J] [DistribMulAction G J]
    {q : ℕ} {φ : G} {𝒯 : Submodule R J}
    (hfrob : ModularCurve.ToricFrobeniusSq q φ 𝒯)
    (ι : V →+ J) (hinj : Function.Injective ι)
    (hequiv : ∀ g : G, ∀ v : V, ι (g • v) = g • ι v)
    (hsub : ∀ v : V, ι v ∈ 𝒯)
    (lam : k) (hscalar : ∀ v : V, φ • v = lam • v)
    (hrank : Module.finrank k V = 2)
    (hdet : LinearMap.det (DistribSMul.toLinearMap k V φ) = (q : k)) :
    (q : k) = 0 ∨ (q : k) = 1 := by sorry
