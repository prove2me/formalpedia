-- Prove2me | Theorems.Thm_NumberField_AdeleRing_principalIdeles_inf_unitIdelesOutside_eq_map_unit
-- name    : NumberField.AdeleRing.principalIdeles_inf_unitIdelesOutside_eq_map_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/3aef356f-53ac-5109-9bce-1ce450a4640d
-- title:
--   Principal idèles in the S-unit idèles are the S-units
-- statement:
--   Let $R$ be a Dedekind domain with fraction field $K$ (so $K$ is an $R$-algebra that is a fraction ring of $R$), and let $S$ be an arbitrary set of height-one primes of $R$. Inside the unit group of the adèle ring $\mathbb{A} =$ `NumberField.AdeleRing R K`, consider two subgroups: [`M4aHerbrand.principalIdeles R K`](def/M4aHerbrand_IdeleClassVocab.html#L16), the image (range of `Units.map`) of $K^\times$ under the diagonal ring homomorphism $K \to \mathbb{A}$; and [`NumberField.AdeleRing.unitIdelesOutside R K S`](def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51), the preimage, under the map on units induced by the projection of $\mathbb{A}$ onto the finite adèle ring, of the subgroup of those finite idèles $\delta$ for which, at every height-one prime $v \notin S$, both the $v$-component of $\delta$ and the $v$-component of $\delta^{-1}$ lie in the valuation ring $\mathcal{O}_v$ of the $v$-adic completion of $K$ (no condition is imposed at $v \in S$ or at the infinite part). The theorem asserts that the intersection of these two subgroups equals the image, under the same map on units induced by $K \to \mathbb{A}$, of Mathlib's $S$-unit subgroup `S.unit K` of $K^\times$, namely the units $u$ of $K$ with $v$-valuation $1$ for every $v \notin S$.
--
--   This identifies the $S$-units of $K$ with the principal idèles that are $S$-unit idèles, the standard first step in comparing $K^\times$-cohomology with idèle-class cohomology. It is used in the capitulation and level arguments for idèle classes and in the proof of the second inequality for prime-norm indices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_principalIdeles_inf_unitIdelesOutside_eq_map_unit.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.AdeleRing.principalIdeles_inf_unitIdelesOutside_eq_map_unit
    (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum R)) :
    M4aHerbrand.principalIdeles R K ⊓ NumberField.AdeleRing.unitIdelesOutside R K S
      = (S.unit K).map (Units.map (algebraMap K (NumberField.AdeleRing R K) :
          K →* NumberField.AdeleRing R K)) := by sorry
