-- Prove2me | Theorems.Thm_GlobalTheory_PlaceExt_wt_add_of_min
-- name    : GlobalTheory.PlaceExt.wt_add_of_min
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:52:33.745535+00:00
-- url     : https://prove2.me/theorems/151c98fd-5d18-4c21-9883-7da4202fe1e1
-- title:
--   Place Ext: wt add of min
-- statement:
--   The Place Ext construction uses the wt add of min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L20-L32

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

theorem GlobalTheory.PlaceExt.wt_add_of_min {a b c : WithTop ℤ} (h : ∀ m : ℕ, ∃ p q r : WithTop ℤ,
    min a (m : ℤ) = min p (m : ℤ) ∧ min b (m : ℤ) = min q (m : ℤ) ∧
      min c (m : ℤ) = min r (m : ℤ) ∧ min p q ≤ r) : min a b ≤ c := by sorry
