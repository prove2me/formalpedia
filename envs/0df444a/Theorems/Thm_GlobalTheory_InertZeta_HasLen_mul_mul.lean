-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_HasLen_mul_mul
-- name    : GlobalTheory.InertZeta.HasLen.mul_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:26:26.638852+00:00
-- url     : https://prove2.me/theorems/4db556bc-b8b2-4a2c-8d19-746816d661f1
-- title:
--   Has Len: mul mul
-- statement:
--   The Has Len construction uses the mul mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasLenOfLatLen.lean#L70-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasLenOfLatLen.lean#L70-L78

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

theorem GlobalTheory.InertZeta.HasLen.mul_mul {g a a' b b' : Matrix (Fin n) (Fin n) L} {k : ℕ} (h : HasLen g k) (ha : IsInt a)
    (ha' : IsInt a') (hb : IsInt b) (hb' : IsInt b') (ea : a' * a = 1) (eb : b * b' = 1) : HasLen (a * g * b) k := by sorry
