-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_len_mul_mul
-- name    : GlobalTheory.InertZeta.len_mul_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:20:02.175811+00:00
-- url     : https://prove2.me/theorems/9e7a2497-3ea2-4493-a62f-a3bb4739cae4
-- title:
--   Inert Zeta: len mul mul
-- statement:
--   The Inert Zeta construction uses the len mul mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasLenOfLatLen.lean#L80-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasLenOfLatLen.lean#L80-L88

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

theorem GlobalTheory.InertZeta.len_mul_mul {g a a' b b' : Matrix (Fin n) (Fin n) L} (ha : IsInt a)
    (ha' : IsInt a') (hb : IsInt b) (hb' : IsInt b') (ea : a' * a = 1) (eb : b * b' = 1) : len (a * g * b) = len g := by sorry
