-- Prove2me | Theorems.Thm_GaussValuationUniqueness_eq_of_le_ht
-- name    : GaussValuationUniqueness.eq_of_le_ht
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:50:52.949599+00:00
-- url     : https://prove2.me/theorems/ab136159-60cb-47e5-aeb5-c60024f3d2f4
-- title:
--   Gauss Valuation Uniqueness: eq of le ht
-- statement:
--   The Gauss Valuation Uniqueness construction uses the eq of le ht property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/ExistsSmulOfLine.lean#L50-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/ExistsSmulOfLine.lean#L50-L59

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

theorem GaussValuationUniqueness.eq_of_le_ht {R : Type*} [CommRing R] [IsDomain R] {Q P : Ideal R} [Q.IsPrime]
    [P.IsPrime] (hP : P.height = 1) (hQ : Q ≠ ⊥) (hle : Q ≤ P) : Q = P := by sorry
