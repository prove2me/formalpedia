-- Prove2me | Theorems.Thm_GlobalTheory_HL_invVol_mul_pos_le_conj
-- name    : GlobalTheory.HL.invVol_mul_pos_le_conj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:00:46.251431+00:00
-- url     : https://prove2.me/theorems/b989fe14-83e9-4c93-9489-98f959c88250
-- title:
--   HL: inv Vol mul pos le conj
-- statement:
--   The HL construction uses the inv Vol mul pos le conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/InvVolMulPosLeConj.lean#L31-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/InvVolMulPosLeConj.lean#L31-L66

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
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
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.invVol_mul_pos_le_conj : ∀ {G : Type} [Group G] (K0 K1 K : Subgroup G),
    K0.relIndex K1 ≠ 0 → K1.relIndex K0 ≠ 0 → K0.relIndex K ≠ 0 → K.relIndex K0 ≠ 0 →
    _root_.GlobalTheory.HL.invVol K0 K = _root_.GlobalTheory.HL.invVol K0 K1 * _root_.GlobalTheory.HL.invVol K1 K ∧
    0 < _root_.GlobalTheory.HL.invVol K0 K ∧
    (K ≤ K1 → _root_.GlobalTheory.HL.invVol K0 K =
      _root_.GlobalTheory.HL.invVol K0 K1 * (K.relIndex K1 : ℝ)) ∧
    ∀ g : G, _root_.GlobalTheory.HL.invVol (MulAut.conj g • K0) (MulAut.conj g • K) =
      _root_.GlobalTheory.HL.invVol K0 K := by sorry
