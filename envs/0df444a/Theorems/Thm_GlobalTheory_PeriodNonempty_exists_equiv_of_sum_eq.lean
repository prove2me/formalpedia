-- Prove2me | Theorems.Thm_GlobalTheory_PeriodNonempty_exists_equiv_of_sum_eq
-- name    : GlobalTheory.PeriodNonempty.exists_equiv_of_sum_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:22.750666+00:00
-- url     : https://prove2.me/theorems/695c3344-f02b-4ea5-86a1-64c436ce85f9
-- title:
--   Period Nonempty: exists equiv of sum eq
-- statement:
--   The Period Nonempty construction uses the exists equiv of sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsEquivOfSumEq.lean#L13-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsEquivOfSumEq.lean#L13-L40

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

theorem GlobalTheory.PeriodNonempty.exists_equiv_of_sum_eq {E : Type} [Field E] [NumberField E] {ι κ : Type} [Fintype ι] [Fintype κ]
    (s : ι → (E →+* ℂ)) (t : κ → (E →+* ℂ)) (h : ∀ a : 𝓞 E, ∑ i, s i (a : E) = ∑ k, t k (a : E)) :
    ∃ e : ι ≃ κ, ∀ i, t (e i) = s i := by sorry
