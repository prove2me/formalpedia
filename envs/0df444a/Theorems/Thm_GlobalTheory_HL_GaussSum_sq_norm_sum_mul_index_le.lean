-- Prove2me | Theorems.Thm_GlobalTheory_HL_GaussSum_sq_norm_sum_mul_index_le
-- name    : GlobalTheory.HL.GaussSum.sq_norm_sum_mul_index_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:32:00.30498+00:00
-- url     : https://prove2.me/theorems/9823c845-b37d-59a1-a998-cf281daa906d
-- title:
--   Gauss Sum: sq norm sum mul index le
-- statement:
--   The Gauss Sum construction uses the sq norm sum mul index le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SqNormSumRepsMulIndexLe.lean#L11-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SqNormSumRepsMulIndexLe.lean#L11-L63

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

theorem GlobalTheory.HL.GaussSum.sq_norm_sum_mul_index_le {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G)
    (f : G → ℂ) (hf : ∀ u, ‖f u‖ = 1)
    (hQ : ∀ h, h ∉ Q → ∃ (v : G) (c : ℂ), c ≠ 1 ∧
      ∀ u, f (u + v + h) * conj (f (u + v)) = c * (f (u + h) * conj (f u))) :
    ‖∑ u, f u‖ ^ 2 * (Q.index : ℝ) ≤ (Fintype.card G : ℝ) ^ 2 := by sorry
