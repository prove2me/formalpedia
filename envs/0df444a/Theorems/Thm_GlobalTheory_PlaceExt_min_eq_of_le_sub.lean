-- Prove2me | Theorems.Thm_GlobalTheory_PlaceExt_min_eq_of_le_sub
-- name    : GlobalTheory.PlaceExt.min_eq_of_le_sub
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:22:45.253095+00:00
-- url     : https://prove2.me/theorems/db005acc-ea57-49fc-b097-8d26cdc31e30
-- title:
--   Place Ext: min eq of le sub
-- statement:
--   The Place Ext construction uses the min eq of le sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L61-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L61-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemIntegralClosureOfMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.PlaceExt
variable {L A : Type*} [Field L] [CommRing A]

theorem GlobalTheory.PlaceExt.min_eq_of_le_sub (u : AddValuation A (WithTop ℤ)) {x y : A} {M : WithTop ℤ}
    (h : M ≤ u (x - y)) : min (u x) M = min (u y) M := by sorry
