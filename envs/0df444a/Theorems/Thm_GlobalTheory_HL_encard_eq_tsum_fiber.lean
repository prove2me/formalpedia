-- Prove2me | Theorems.Thm_GlobalTheory_HL_encard_eq_tsum_fiber
-- name    : GlobalTheory.HL.encard_eq_tsum_fiber
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:15:43.294068+00:00
-- url     : https://prove2.me/theorems/4206c19a-f0ea-4ed3-b51b-323ce397049a
-- title:
--   HL: encard eq tsum fiber
-- statement:
--   The HL construction uses the encard eq tsum fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MassOrbitsEqTsumFiber.lean#L10-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MassOrbitsEqTsumFiber.lean#L10-L23

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MassOrbitsEqTsumFiber
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL

theorem GlobalTheory.HL.encard_eq_tsum_fiber {X Z : Type*} (q : X → Z) (Q : X → Prop) :
    (({x | Q x} : Set X).encard : ℝ≥0∞)
      = ∑' z : Z, (({x | q x = z ∧ Q x} : Set X).encard : ℝ≥0∞) := by sorry
