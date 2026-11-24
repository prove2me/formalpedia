-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_IsFrac_v_det_le
-- name    : GlobalTheory.InertZeta.IsFrac.v_det_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:21:17.657608+00:00
-- url     : https://prove2.me/theorems/26c62ae2-af29-4de4-93ac-088bd2e28964
-- title:
--   Is Frac: v det le
-- statement:
--   The Is Frac construction uses the v det le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasLenOfLatLen.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasLenOfLatLen.lean#L45-L50

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem GlobalTheory.InertZeta.IsFrac.v_det_le {g U V C U' V' C' : Matrix (Fin n) (Fin n) L} (h : IsFrac g U V C) (h' : IsFrac g U' V' C') :
    Valued.v C'.det ≤ Valued.v C.det := by sorry
