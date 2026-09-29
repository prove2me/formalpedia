-- Prove2me | Theorems.Thm_NumberField_AdeleRing_finite_setOf_valued_snd_ne_one
-- name    : NumberField.AdeleRing.finite_setOf_valued_snd_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/5e374f4c-4cab-5d98-a340-755215c82d46
-- title:
--   An idèle is a local unit at almost all finite places
-- statement:
--   Let $K$ be a number field, i.e. a field of characteristic zero that is a finite extension of $\mathbb{Q}$ in the sense of Mathlib's `NumberField` class, and let $x$ be a unit of the adèle ring $\mathbb{A}_K =$ `AdeleRing (𝓞 K) K` of $K$ over its ring of integers $\mathcal{O}_K$. Writing the underlying adèle of $x$ as a pair, its second component $x.2$ is the finite-adèle part, an element of `FiniteAdeleRing (𝓞 K) K`, namely the restricted product of the completions $K_w$ with respect to their valuation rings, indexed by the height-one primes $w$ of $\mathcal{O}_K$. The assertion is that the set of height-one primes $w$ of $\mathcal{O}_K$ at which the $w$-component of this finite adèle has $w$-adic valuation different from $1$, that is $\{w : \mathrm{v}_w\big((x.2)_w\big) \neq 1\}$ with values in $\mathbb{Z}^{\mathrm{mult}} \cup \{0\}$, is a finite set. Equivalently, a finite idèle that is a unit is a unit of the valuation ring $\mathcal{O}_{K_w}$ at all but finitely many $w$.
--
--   This is the standard finiteness underlying the description of the idèle group as a restricted product of the local unit groups: an idèle is a local unit outside a finite set of places. It is used when passing from idèles to finitely supported valuation vectors, and is cited by [`NumberField.AdeleRing.exists_forall_mul_inv_smul_div_mem_unitIdelesOutside_of_forall_mem`](thm.html#NumberField.AdeleRing.exists_forall_mul_inv_smul_div_mem_unitIdelesOutside_of_forall_mem) and by [`NumberField.SIdele.existsUnique_map_eq_of_forall_map_prG_eq_zero`](thm.html#NumberField.SIdele.existsUnique_map_eq_of_forall_map_prG_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_finite_setOf_valued_snd_ne_one.lean

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

theorem NumberField.AdeleRing.finite_setOf_valued_snd_ne_one
    (K : Type) [Field K] [NumberField K] (x : (AdeleRing (𝓞 K) K)ˣ) :
    {w : HeightOneSpectrum (𝓞 K) | Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) ≠ 1}.Finite := by sorry
