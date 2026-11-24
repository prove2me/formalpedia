-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_antiJ_mul_apply
-- name    : GlobalTheory.SatakeWeyl.antiJ_mul_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:06:39.926321+00:00
-- url     : https://prove2.me/theorems/e44ee471-c749-43de-ad25-bcf2b834e7ef
-- title:
--   Satake Weyl: anti J mul apply
-- statement:
--   The Satake Weyl construction uses the anti J mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AntiJMulApply.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AntiJMulApply.lean#L37-L44

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
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
open Formalism.UG
open GlobalTheory GlobalTheory.SatakeWeyl
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem GlobalTheory.SatakeWeyl.antiJ_mul_apply (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) : (antiJ L n * M) i j = M i.rev j := by sorry
