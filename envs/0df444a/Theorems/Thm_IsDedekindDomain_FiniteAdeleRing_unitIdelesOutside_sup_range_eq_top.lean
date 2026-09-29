-- Prove2me | Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_unitIdelesOutside_sup_range_eq_top
-- name    : IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside_sup_range_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/b241ff4f-aaf2-512a-b062-1ca3c5b9a193
-- title:
--   Finite idèles: S-units together with K^× generate everything
-- statement:
--   Let $R$ be a Dedekind domain with fraction field $K$ (so $K$ is a field, an $R$-algebra, and a fraction field of $R$), and let $S$ be a set of height-one primes of $R$. Assume that $S$ captures every ideal class: for each $c$ in the class group of $R$ there is an ideal $I$ of $R$ that is a non-zero-divisor in the monoid of ideals, whose class `ClassGroup.mk0 I` equals $c$, and such that every height-one prime $v$ with $v.\mathrm{asIdeal}$ dividing $I$ lies in $S$. The conclusion concerns two subgroups of the unit group of the finite adèle ring `FiniteAdeleRing R K`: first, `unitIdelesOutside R K S`, the subgroup of those units $\delta$ such that at every $v \notin S$ both the component $\delta_v$ and the component of $\delta^{-1}$ at $v$ lie in the valuation ring $\mathcal{O}_v$ of the completion at $v$; second, the image of $K^\times$ under the map of unit groups induced by the structural map $K \to$ `FiniteAdeleRing R K`. The theorem asserts that the join of these two subgroups is the whole group of finite idèles.
--
--   This is the finite-adèlic form of the classical decomposition $J_K = K^\times J_{K,S}$ valid whenever $S$ contains primes generating the ideal class group, stated here for an arbitrary Dedekind domain. It is used to derive the corresponding statement for the full adèle ring of a number field, [`NumberField.AdeleRing.principalIdeles_sup_unitIdelesOutside_eq_top`](thm.html#NumberField.AdeleRing.principalIdeles_sup_unitIdelesOutside_eq_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_FiniteAdeleRing_unitIdelesOutside_sup_range_eq_top.lean

import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped nonZeroDivisors

theorem IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside_sup_range_eq_top
    (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum R))
    (hS : ∀ c : ClassGroup R, ∃ I : (Ideal R)⁰, ClassGroup.mk0 I = c ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum R, v.asIdeal ∣ (I : Ideal R) → v ∈ S) :
    IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K S ⊔
      (Units.map (algebraMap K (IsDedekindDomain.FiniteAdeleRing R K) :
        K →* IsDedekindDomain.FiniteAdeleRing R K)).range = ⊤ := by sorry
