-- Prove2me | Theorems.Thm_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber
-- name    : NumberField.TateGlobal.index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/47e62ff9-c936-5dfd-9016-253eaa4c115e
-- title:
--   Index of K^×·(K_∞^××widehat𝒪^×) is h_K
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal O_K$ and adele ring $\mathbb A_K = \mathbb A_{K,\infty}\times \mathbb A_K^f$ (a product of the infinite adele ring and the finite adele ring of $\mathcal O_K$ in $K$). Consider two subgroups of the unit group $\mathbb A_K^\times$. The first is [`NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K ∅`](def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51), the preimage, under the map on units induced by the projection $\mathbb A_K\to\mathbb A_K^f$, of the subgroup of those units $\delta$ of the finite adele ring such that for every height-one prime $v$ of $\mathcal O_K$ — the exceptional set being empty, so the condition is imposed at all $v$ — both $\delta_v$ and $(\delta^{-1})_v$ lie in the valuation ring $\mathcal O_v$ of the $v$-adic completion; that is, the ideles whose finite component is a unit of $\mathcal O_v$ at every finite place, with arbitrary archimedean component. The second is the range of the map on unit groups induced by the structure map $K\to\mathbb A_K$, i.e. the group of principal ideles $K^\times$. The assertion is that the index of the join of these two subgroups in $\mathbb A_K^\times$ is the class number of $K$ (which is `NumberField.classNumber K`, the cardinality of the class group of $\mathcal O_K$); in particular this index is finite.
--
--   This is the adelic description of the ideal class group in the form used in Tate's thesis: $\mathbb A_K^\times/(K^\times\cdot(K_\infty^\times\times\prod_v\mathcal O_v^\times))\cong \mathrm{Cl}(\mathcal O_K)$, read off here as an index. It feeds the global volume computation, where the measure of a fundamental domain intersected with a norm interval is expressed in terms of the unit shell, the class number and the regulator.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem NumberField.TateGlobal.index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber
    (K : Type) [Field K] [NumberField K] :
    (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (∅ : Set (HeightOneSpectrum (𝓞 K))) ⊔
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range).index =
      NumberField.classNumber K := by sorry
