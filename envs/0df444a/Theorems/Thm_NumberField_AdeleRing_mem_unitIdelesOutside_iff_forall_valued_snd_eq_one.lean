-- Prove2me | Theorems.Thm_NumberField_AdeleRing_mem_unitIdelesOutside_iff_forall_valued_snd_eq_one
-- name    : NumberField.AdeleRing.mem_unitIdelesOutside_iff_forall_valued_snd_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/c60d38d2-d6ec-5b85-9b4e-b6293bd3bcbc
-- title:
--   Unit idèles outside T characterised by valuations
-- statement:
--   Let $K$ be a number field, let $T$ be a set of height-one primes of the ring of integers $\mathcal{O}_K$, and let $x$ be a unit of the adèle ring $\mathbb{A}_K$ of $K$ (the product of the infinite adèle ring with the finite adèle ring). Then $x$ lies in the subgroup [`NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K T`](def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51) — that is, the image of $x$ under the map on unit groups induced by the second projection $\mathbb{A}_K \to \mathbb{A}_{K,\mathrm{fin}}$ lies in the subgroup of finite idèles $\delta$ such that for every height-one prime $v \notin T$ both the $v$-component of $\delta$ and the $v$-component of $\delta^{-1}$ belong to the valuation ring $\mathcal{O}_{K_v}$ of the $v$-adic completion — if and only if for every height-one prime $w \notin T$ the $w$-adic valuation of the $w$-component of the finite part of $x$ equals $1$.
--
--   This identifies the group of idèles that are units at all finite places outside $T$ (the "unit idèles outside $T$", in the classical terminology of $S$-idèle theory) by the valuation condition $|x_w|_w = 1$ off $T$, replacing the two-sided integrality condition in the definition by a single equality. It is used in the approximation and Artin-symbol computations for the idèle class group that rely on this subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_mem_unitIdelesOutside_iff_forall_valued_snd_eq_one.lean

import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport

theorem NumberField.AdeleRing.mem_unitIdelesOutside_iff_forall_valued_snd_eq_one
    (K : Type) [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K))) (x : (AdeleRing (𝓞 K) K)ˣ) :
    x ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K T ↔
      ∀ w : HeightOneSpectrum (𝓞 K), w ∉ T →
        Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1 := by sorry
