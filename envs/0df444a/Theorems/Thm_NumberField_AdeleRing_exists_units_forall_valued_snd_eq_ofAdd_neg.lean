-- Prove2me | Theorems.Thm_NumberField_AdeleRing_exists_units_forall_valued_snd_eq_ofAdd_neg
-- name    : NumberField.AdeleRing.exists_units_forall_valued_snd_eq_ofAdd_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/e7402331-97b3-54fa-8cd9-372e416280b4
-- title:
--   An idèle with prescribed valuations at all finite places
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$, and let $m$ be a finitely supported function from the height one spectrum of $\mathcal{O}_K$ (that is, the nonzero prime ideals, equivalently the finite places of $K$) to $\mathbb{Z}$. The assertion is that there exists a unit $q$ of the adèle ring `AdeleRing (𝓞 K) K`, which is the product of the infinite adèle ring of $K$ with the finite adèle ring of $\mathcal{O}_K$ in $K$, such that for every finite place $w$ the $w$-component of the finite part $q.2$ of $q$, an element of the completion $K_w$, has valuation exactly $\mathrm{ofAdd}(-m(w))$ in $\mathbb{Z}^{\mathrm{mult}} \cup \{0\}$, where the valuation is the canonical $\mathbb{Z}$-valued one on $K_w$ normalised so that a uniformiser has valuation $\mathrm{ofAdd}(-1)$. Equivalently: $q$ is an idèle whose finite components are $\pi_w^{m(w)}$ up to units, no condition being imposed on the archimedean components.
--
--   This is the standard surjectivity statement for the map from the idèle group to the group of fractional ideals (or divisors) of $K$: every finitely supported assignment of integer exponents to the finite places is realised by an idèle. It is used in the construction of $S$-idèle and unit-idèle decompositions, being cited by [`NumberField.AdeleRing.exists_forall_mul_inv_smul_div_mem_unitIdelesOutside_of_forall_mem`](thm.html#NumberField.AdeleRing.exists_forall_mul_inv_smul_div_mem_unitIdelesOutside_of_forall_mem) and by [`NumberField.SIdele.existsUnique_map_eq_of_forall_map_prG_eq_zero`](thm.html#NumberField.SIdele.existsUnique_map_eq_of_forall_map_prG_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_exists_units_forall_valued_snd_eq_ofAdd_neg.lean

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

theorem NumberField.AdeleRing.exists_units_forall_valued_snd_eq_ofAdd_neg
    (K : Type) [Field K] [NumberField K] (m : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    ∃ q : (AdeleRing (𝓞 K) K)ˣ, ∀ w : HeightOneSpectrum (𝓞 K),
      Valued.v (((q : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) =
        ((Multiplicative.ofAdd (-(m w)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by sorry
