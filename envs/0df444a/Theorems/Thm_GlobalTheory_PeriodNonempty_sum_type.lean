-- Prove2me | Theorems.Thm_GlobalTheory_PeriodNonempty_sum_type
-- name    : GlobalTheory.PeriodNonempty.sum_type
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:17:14.343164+00:00
-- url     : https://prove2.me/theorems/78816591-c4b8-47de-9a6d-3758dd03e60c
-- title:
--   Period Nonempty: sum type
-- statement:
--   The Period Nonempty construction uses the sum type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsEquivOfSumEq.lean#L171-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsEquivOfSumEq.lean#L171-L219

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodNonempty
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.PeriodNonempty.sum_type (H : Host E) {p q g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H p q ty) (a : E) :
    ∑ i, ty i a = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
      ((p : ℂ) * τ a + (q : ℂ) * starRingEnd ℂ (τ a)) := by sorry
