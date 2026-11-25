-- Prove2me | Theorems.Thm_GlobalTheory_PlaceExt_le_val_pow_mul
-- name    : GlobalTheory.PlaceExt.le_val_pow_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:31:37.40123+00:00
-- url     : https://prove2.me/theorems/26e1eaaf-3a1f-4a96-b9a8-2b7fc14e524c
-- title:
--   Place Ext: le val pow mul
-- statement:
--   The Place Ext construction uses the le val pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L51-L59

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

theorem GlobalTheory.PlaceExt.le_val_pow_mul (u : AddValuation A (WithTop ℤ)) {t b : A} (ht : 1 ≤ u t) (hb : 0 ≤ u b)
    (m : ℕ) : ((m : ℤ) : WithTop ℤ) ≤ u (t ^ m * b) := by sorry
