-- Prove2me | Theorems.Thm_IharaLemma_resKer_localized
-- name    : IharaLemma.resKer_localized
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/ec463e2c-9d1c-5653-b2ce-07f5f3f6bbcf
-- title:
--   Kernel bound ker(red)⊆varpi V localises
-- statement:
--   Let $R$ be a commutative ring, $S$ a submonoid of $R$, and let $V$, $V_k$, $V'$, $V_k'$ be $R$-modules (abelian groups with $R$-module structures). Fix an element $\varpi \in R$ and an $R$-linear map $\mathrm{redV} : V \to V_k$ satisfying the kernel bound: every $v \in V$ with $\mathrm{redV}(v) = 0$ is of the form $v = \varpi \cdot v_1$ for some $v_1 \in V$. Let $g_V : V \to V'$ and $g_K : V_k \to V_k'$ be $R$-linear maps exhibiting $V'$ and $V_k'$ as localisations of $V$ and of $V_k$ at $S$, in the sense of Mathlib's `IsLocalizedModule S`. Let $\mathrm{red}' : V' \to V_k'$ be an $R$-linear map making the square commute on the nose, i.e. $\mathrm{red}'(g_V(v)) = g_K(\mathrm{redV}(v))$ for all $v \in V$. The conclusion is that the same kernel bound holds downstairs: for every $v' \in V'$ with $\mathrm{red}'(v') = 0$ there exists $v_1' \in V'$ with $v' = \varpi \cdot v_1'$.
--
--   This is the statement that a bound of the form $\ker(\mathrm{red}) \subseteq \varpi V$ is preserved under localisation of both source and target at a multiplicative set, the divisibility statement being the module-theoretic shadow of exactness of localisation. It is used in the level-raising/Ihara-type part of the argument, where such kernel bounds for reduction maps on spaces of modular forms must be transported to localised Hecke modules; it is cited by [`CohCarrier.injective_and_residual_of_isEis`](thm.html#CohCarrier.injective_and_residual_of_isEis) and [`CuspForm.AuxLevel.exists_linearEquiv_baseML_prod_ML`](thm.html#CuspForm.AuxLevel.exists_linearEquiv_baseML_prod_ML).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaLemma_resKer_localized.lean

import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IharaLemma.resKer_localized {R : Type*} [CommRing R] (S : Submonoid R) {V Vk V' Vk' : Type*}
    [AddCommGroup V] [Module R V] [AddCommGroup Vk] [Module R Vk]
    [AddCommGroup V'] [Module R V'] [AddCommGroup Vk'] [Module R Vk']
    (ϖ : R) (redV : V →ₗ[R] Vk)
    (hker : ∀ v, redV v = 0 → ∃ v₁, v = ϖ • v₁)
    (gV : V →ₗ[R] V') [IsLocalizedModule S gV] (gK : Vk →ₗ[R] Vk') [IsLocalizedModule S gK]
    (red' : V' →ₗ[R] Vk') (hsq : ∀ v, red' (gV v) = gK (redV v)) :
    ∀ v' : V', red' v' = 0 → ∃ v₁' : V', v' = ϖ • v₁' := by sorry
