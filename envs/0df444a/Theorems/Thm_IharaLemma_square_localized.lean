-- Prove2me | Theorems.Thm_IharaLemma_square_localized
-- name    : IharaLemma.square_localized
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/12853fa4-a4d3-5c08-a9af-d22b0c13938e
-- title:
--   Commuting squares of modules descend to localisations
-- statement:
--   Let $R$ be a commutative ring and $S \subseteq R$ a submonoid, and let $V, V_k, V', V_k', L, L', L_k, L_k'$ be $R$-modules. Given $R$-linear maps $f : V \to L$, $\mathrm{red}_V : V \to V_k$, $\mathrm{red}_L : L \to L_k$ and $f_k : V_k \to L_k$ whose square commutes pointwise, i.e. $\mathrm{red}_L(f v) = f_k(\mathrm{red}_V v)$ for all $v \in V$; given further $R$-linear maps $g_V : V \to V'$, $g_K : V_k \to V_k'$ and $g_{L_k} : L_k \to L_k'$, each exhibiting its target as a localisation of its source at $S$ (`IsLocalizedModule S`), and an arbitrary $R$-linear map $g_L : L \to L'$ with no localisation hypothesis; and given $R$-linear maps $f' : V' \to L'$, $\mathrm{red}_V' : V' \to V_k'$, $\mathrm{red}_L' : L' \to L_k'$ and $f_k' : V_k' \to L_k'$ which lie over $f$, $\mathrm{red}_V$, $\mathrm{red}_L$ and $f_k$ respectively, in the sense that $f'(g_V v) = g_L(f v)$, $\mathrm{red}_V'(g_V v) = g_K(\mathrm{red}_V v)$, $\mathrm{red}_L'(g_L x) = g_{L_k}(\mathrm{red}_L x)$ and $f_k'(g_K y) = g_{L_k}(f_k y)$ for all $v \in V$, $x \in L$, $y \in V_k$: then the localised square commutes, i.e. $\mathrm{red}_L'(f' v') = f_k'(\mathrm{red}_V' v')$ for every $v' \in V'$.
--
--   A bookkeeping lemma on localisation of modules: commutativity of a square of $R$-linear maps, together with compatibility of the four maps with the localisation maps, forces the induced square on localisations to commute. It is used in the setting where the vertical maps are reductions modulo a prime, in the injectivity-and-reduction step for cohomological carriers and in the construction of a linear equivalence between auxiliary-level cusp form modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaLemma_square_localized.lean

import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IharaLemma.square_localized {R : Type*} [CommRing R] (S : Submonoid R) {V Vk V' Vk' L L' Lk Lk' : Type*}
    [AddCommGroup V] [Module R V] [AddCommGroup Vk] [Module R Vk]
    [AddCommGroup V'] [Module R V'] [AddCommGroup Vk'] [Module R Vk']
    [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
    [AddCommGroup Lk] [Module R Lk] [AddCommGroup Lk'] [Module R Lk']
    (f : V →ₗ[R] L) (redV : V →ₗ[R] Vk) (redL : L →ₗ[R] Lk) (fk : Vk →ₗ[R] Lk)
    (hsq : ∀ v, redL (f v) = fk (redV v))
    (gV : V →ₗ[R] V') [IsLocalizedModule S gV] (gK : Vk →ₗ[R] Vk') [IsLocalizedModule S gK]
    (gL : L →ₗ[R] L') (gLk : Lk →ₗ[R] Lk') [IsLocalizedModule S gLk]
    (f' : V' →ₗ[R] L') (hf' : ∀ v, f' (gV v) = gL (f v))
    (redV' : V' →ₗ[R] Vk') (hredV' : ∀ v, redV' (gV v) = gK (redV v))
    (redL' : L' →ₗ[R] Lk') (hredL' : ∀ x, redL' (gL x) = gLk (redL x))
    (fk' : Vk' →ₗ[R] Lk') (hfk' : ∀ y, fk' (gK y) = gLk (fk y)) :
    ∀ v', redL' (f' v') = fk' (redV' v') := by sorry
