-- Prove2me | Theorems.Thm_GaussValuationUniqueness_pos_of_not_isUnit
-- name    : GaussValuationUniqueness.pos_of_not_isUnit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:51:33.496364+00:00
-- url     : https://prove2.me/theorems/d5f50a03-08a6-41db-85fe-70216646f7f1
-- title:
--   Gauss Valuation Uniqueness: pos of not is Unit
-- statement:
--   The Gauss Valuation Uniqueness construction uses the pos of not is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/ExistsSmulOfLine.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/ExistsSmulOfLine.lean#L18-L32

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

theorem GaussValuationUniqueness.pos_of_not_isUnit {Ω : Type*} [Field Ω] (v : AddValuation Ω (WithTop ℤ))
    (x : vRing v) (hx : ¬ IsUnit x) : 0 < v (x : Ω) := by sorry
