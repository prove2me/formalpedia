-- Prove2me | Theorems.Thm_GaussValuationUniqueness_mem_vRing_iff
-- name    : GaussValuationUniqueness.mem_vRing_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:50.646043+00:00
-- url     : https://prove2.me/theorems/b5808f40-c8c8-42b8-9a9a-370b45c6e638
-- title:
--   Gauss Valuation Uniqueness: mem v Ring iff
-- statement:
--   The Gauss Valuation Uniqueness construction uses the mem v Ring iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/ExistsSmulOfLine.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/ExistsSmulOfLine.lean#L7-L9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ExistsSmulOfLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GaussValuationUniqueness
open ReciprocityTheory.ChartRestriction.G.T0

theorem GaussValuationUniqueness.mem_vRing_iff {Ω : Type*} [Field Ω] (v : AddValuation Ω (WithTop ℤ)) (x : Ω) :
    x ∈ vRing v ↔ 0 ≤ v x := by sorry
