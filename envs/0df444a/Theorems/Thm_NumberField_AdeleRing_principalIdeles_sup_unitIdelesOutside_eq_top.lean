-- Prove2me | Theorems.Thm_NumberField_AdeleRing_principalIdeles_sup_unitIdelesOutside_eq_top
-- name    : NumberField.AdeleRing.principalIdeles_sup_unitIdelesOutside_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/ae9abc25-eb58-5f27-8b9b-510e98b45d80
-- title:
--   Every idele is principal times an S-unit idele
-- statement:
--   Let $R$ be a Dedekind domain, $K$ a field equipped with an $R$-algebra structure making it the fraction field of $R$, and let $S$ be a set of height-one primes of $R$. Assume that every ideal class $c \in \mathrm{ClassGroup}(R)$ is represented by a nonzero integral ideal $I$ of $R$ (an element of the monoid of non-zero-divisors of $\mathrm{Ideal}\,R$) with $\mathrm{ClassGroup.mk}_0(I) = c$ all of whose prime divisors lie in $S$. Then the two subgroups of the unit group $(\mathbb{A}_K)^\times$ of the adele ring $\mathbb{A}_K = \mathbb{A}_K^\infty \times \mathbb{A}_{K,\mathrm{fin}}$ generate everything: the join [`M4aHerbrand.principalIdeles R K`](def/M4aHerbrand_IdeleClassVocab.html#L16) $\sqcup$ [`NumberField.AdeleRing.unitIdelesOutside R K S`](def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51) equals $\top$. Here `principalIdeles` is the image of $K^\times$ under the unit map induced by $\mathrm{algebraMap}\colon K \to \mathbb{A}_K$, and `unitIdelesOutside` is the preimage, under the projection of adele units onto finite-adele units, of the subgroup of those finite ideles $\delta$ such that for every height-one prime $v \notin S$ both the $v$-component of $\delta$ and the $v$-component of $\delta^{-1}$ lie in the valuation ring $\mathcal{O}_v$ of the $v$-adic completion; no condition is imposed at the archimedean factor or at primes in $S$.
--
--   This is the classical statement $J_K = K^\times J_{K,S}$ for a set $S$ of primes whose classes generate the class group, here in its full-adele (rather than finite-adele) form. It is used in the computation of Herbrand quotients for idele class groups, being cited in the construction of cyclotomic extensions realising norm indices and in the proof of the second inequality for prime norm indices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_principalIdeles_sup_unitIdelesOutside_eq_top.lean

import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped nonZeroDivisors

theorem NumberField.AdeleRing.principalIdeles_sup_unitIdelesOutside_eq_top
    (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum R))
    (hS : ∀ c : ClassGroup R, ∃ I : (Ideal R)⁰, ClassGroup.mk0 I = c ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum R, v.asIdeal ∣ (I : Ideal R) → v ∈ S) :
    M4aHerbrand.principalIdeles R K ⊔ NumberField.AdeleRing.unitIdelesOutside R K S = ⊤ := by sorry
