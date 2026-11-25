-- Prove2me | Theorems.Thm_GlobalTheory_HL_GaussSum_sq_norm_sum_reps_mul_index_le
-- name    : GlobalTheory.HL.GaussSum.sq_norm_sum_reps_mul_index_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:09:25.864379+00:00
-- url     : https://prove2.me/theorems/e476c9ca-8477-4976-8a1a-5dae60bb965f
-- title:
--   Gauss Sum: sq norm sum reps mul index le
-- statement:
--   The Gauss Sum construction uses the sq norm sum reps mul index le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SqNormSumRepsMulIndexLe.lean#L65-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SqNormSumRepsMulIndexLe.lean#L65-L130

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqNormSumRepsMulIndexLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GaussSum

theorem GlobalTheory.HL.GaussSum.sq_norm_sum_reps_mul_index_le {M : Type*} [AddCommGroup M] (P Q : AddSubgroup M)
    (hPQ : P ≤ Q) (R : Finset M) (hR : ∀ u, ∃! w, w ∈ R ∧ u - w ∈ P)
    (f : M → ℂ) (hf : ∀ u, ‖f u‖ = 1) (hP : ∀ u, ∀ p ∈ P, f (u + p) = f u)
    (hQ : ∀ h, h ∉ Q → ∃ (v : M) (c : ℂ), c ≠ 1 ∧
      ∀ u, f (u + v + h) * conj (f (u + v)) = c * (f (u + h) * conj (f u))) :
    ‖∑ u ∈ R, f u‖ ^ 2 * (Q.index : ℝ) ≤ (R.card : ℝ) ^ 2 := by sorry
