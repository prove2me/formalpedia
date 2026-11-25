-- Prove2me | Theorems.Thm_GlobalTheory_PlaceExt_wt_mul_of_min
-- name    : GlobalTheory.PlaceExt.wt_mul_of_min
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:52:15.553374+00:00
-- url     : https://prove2.me/theorems/b544b3db-fae2-4eb8-a9c9-bfa0294c2300
-- title:
--   Place Ext: wt mul of min
-- statement:
--   The Place Ext construction uses the wt mul of min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L34-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L34-L45

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

theorem GlobalTheory.PlaceExt.wt_mul_of_min {a b c : WithTop ℤ} (n : ℕ) (h : ∀ m : ℕ, ∃ p q : WithTop ℤ,
    min a ((m + n : ℕ) : ℤ) = min p ((m + n : ℕ) : ℤ) ∧
      min b ((m + n : ℕ) : ℤ) = min q ((m + n : ℕ) : ℤ) ∧
      min c (m : ℤ) = min (p + q) (m : ℤ)) : c = a + b := by sorry
