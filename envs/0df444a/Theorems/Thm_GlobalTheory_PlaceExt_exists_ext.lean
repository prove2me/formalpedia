-- Prove2me | Theorems.Thm_GlobalTheory_PlaceExt_exists_ext
-- name    : GlobalTheory.PlaceExt.exists_ext
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:50:20.131546+00:00
-- url     : https://prove2.me/theorems/d4671817-9cf7-54d0-b731-ee807e4291e8
-- title:
--   Place Ext: exists ext
-- statement:
--   The Place Ext construction uses the exists ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L85-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L85-L162

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
variable (ι : L →+* A) (S : Subring A) (π : L) (w : AddValuation L (WithTop ℤ))

theorem GlobalTheory.PlaceExt.exists_ext (hπ0 : π ≠ 0) (hπS : ι π ∈ S) (hw : 1 ≤ w π)
    (hS : ∀ l, ι l ∈ S → 0 ≤ w l)
    (happ : ∀ (x : A) (m : ℕ), ∃ l, ∃ b ∈ S, x - ι l = ι π ^ m * b)
    (hden : ∀ x : A, ∃ n : ℕ, ι π ^ n * x ∈ S) :
    ∃ u : AddValuation A (WithTop ℤ), (∀ l, u (ι l) = w l) ∧ ∀ b ∈ S, 0 ≤ u b := by sorry
