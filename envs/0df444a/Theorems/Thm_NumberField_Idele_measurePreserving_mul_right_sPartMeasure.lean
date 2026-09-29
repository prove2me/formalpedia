-- Prove2me | Theorems.Thm_NumberField_Idele_measurePreserving_mul_right_sPartMeasure
-- name    : NumberField.Idele.measurePreserving_mul_right_sPartMeasure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/c66451b2-c92a-5c8f-85a8-efd16ea28702
-- title:
--   Right translation invariance of the S-part idelic measure
-- statement:
--   Let $K$ be a number field, $S$ a finite set of height-one primes of the ring of integers $\mathcal{O}_K$, and $u$ a unit of the adele ring $\mathbb{A}_K = \mathrm{AdeleRing}(\mathcal{O}_K, K)$ whose finite component satisfies $u_v = 1$ for every height-one prime $v \notin S$. The unit group $\mathbb{A}_K^\times$ carries the Borel $\sigma$-algebra of its topology, and [`NumberField.Idele.sPartMeasure K S`](def/NumberField_IdeleProductMeasure.html#L458) is the measure obtained by pushing forward, along the monoid homomorphism [`NumberField.Idele.partAt K S`](def/NumberField_IdeleProductMeasure.html#L90) (the map induced on units by the adelic truncation `partAtAdele` at $S$), the idelic Haar measure [`NumberField.Idele.idelicHaar K`](def/NumberField_IdeleProductMeasure.html#L391) restricted to the set underlying the subgroup [`NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K S`](def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51), that is, to the ideles $\delta$ such that for every $v \notin S$ both the finite component $\delta_v$ and the finite component $(\delta^{-1})_v$ lie in the valuation ring $\mathcal{O}_{K_v}$. The assertion is that right multiplication $t \mapsto t\,u$ on $\mathbb{A}_K^\times$ is measure preserving for this measure: the map is measurable and its push-forward of `sPartMeasure K S` is again `sPartMeasure K S`.
--
--   This is the translation invariance of the $S$-part measure on the idele group under ideles that are trivial at the finite places outside $S$; it is the invariance property that allows shifts of the integration variable in local computations. It is used in the Rankin–Selberg integral manipulations (comparison of a torus integral with an archimedean torus integral) and in the factorisation of integrals of $S$-parts occurring in the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_measurePreserving_mul_right_sPartMeasure.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal Classical

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem NumberField.Idele.measurePreserving_mul_right_sPartMeasure
    (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (u : (AdeleRing (𝓞 K) K)ˣ) (_huS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((u : AdeleRing (𝓞 K) K)).2 v = 1) :
    MeasurePreserving (fun t : (AdeleRing (𝓞 K) K)ˣ => t * u) (NumberField.Idele.sPartMeasure K S) (NumberField.Idele.sPartMeasure K S) := by sorry
