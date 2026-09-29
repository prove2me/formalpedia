-- Prove2me | Theorems.Thm_NumberField_AdeleRing_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_isScalarTower
-- name    : NumberField.AdeleRing.unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_isScalarTower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/8ab32160-0d03-5a47-a1d3-159272e9b9f0
-- title:
--   Genuine base change preserves S-unit idèles and S-units
-- statement:
--   Let $E \subseteq K \subseteq K''$ be number fields, given as fields $E$, $K$, $K''$ with algebra structures $E \to K$, $K \to K''$, $E \to K''$ forming a scalar tower, and let $S$ be a finite set of nonzero primes of $\mathcal O_E$. The assertion is a conjunction. First, let $\beta$ be the ring homomorphism $\mathbb A_K \to \mathbb A_{K''}$ underlying [`M4aHerbrand.GenuineDescent.genuineBaseChange K K''`](def/M4aHerbrand_GenuineDescent.html#L87); then for every unit $x$ of $\mathbb A_K$ whose finite part $\delta$ satisfies, at every prime $v$ of $\mathcal O_K$ with $v \cap \mathcal O_E \notin S$, that both $\delta_v$ and $(\delta^{-1})_v$ lie in the valuation ring of the completion $K_v$, the unit $\beta(x)$ of $\mathbb A_{K''}$ has the same property at every prime $w$ of $\mathcal O_{K''}$ with $w \cap \mathcal O_E \notin S$. Secondly, for every element $x$ of the underlying module of the $\mathbb Z$-representation [`NumberField.SUnits.sUnitsRep E K S`](def/NumberField_SUnitsModule.html#L52) of $K \simeq_E K$ there is an element $x''$ of [`NumberField.SUnits.sUnitsRep E K'' S`](def/NumberField_SUnitsModule.html#L52) whose associated unit of $K''$ is the image of the unit $\mathrm{val}(x) \in K^\times$ under $\mathrm{algebraMap}\,K\,K''$.
--
--   This records the compatibility of the genuine adèlic base change with the $S$-integrality conditions defining the unit idèles outside $S$, together with the elementary inclusion of $S$-units of $K$ into $S$-units of $K''$, for $S$ a finite set of primes of the common base $E$. It is used in the construction of local invariants for $S$-idèle classes, namely by [`NumberField.IdeleLocalInv.exists_cocyclesTwo_sUnitsRep_map_toUnitsRep_eq_of_capitulation`](thm.html#NumberField.IdeleLocalInv.exists_cocyclesTwo_sUnitsRep_map_toUnitsRep_eq_of_capitulation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_isScalarTower.lean

import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

theorem NumberField.AdeleRing.unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_isScalarTower
    (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K'']
    (S : Finset (HeightOneSpectrum (𝓞 E))) :
    (∀ x : (AdeleRing (𝓞 K) K)ˣ,
      x ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S} →
      Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K K'').β.toMonoidHom x ∈
        NumberField.AdeleRing.unitIdelesOutside (𝓞 K'') K'' {w | w.under (𝓞 E) ∈ S}) ∧
    (∀ x : NumberField.SUnits.sUnitsRep E K S, ∃ x'' : NumberField.SUnits.sUnitsRep E K'' S,
      NumberField.SUnits.val E K'' S x'' = Units.map (algebraMap K K'' : K →* K'') (NumberField.SUnits.val E K S x)) := by sorry
