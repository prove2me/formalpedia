-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_exists_mat
-- name    : GlobalTheory.SatakeWeyl.exists_mat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:09:32.757803+00:00
-- url     : https://prove2.me/theorems/876d3588-9759-4bf4-9b4b-a58be76ab170
-- title:
--   Satake Weyl: exists mat
-- statement:
--   The Satake Weyl construction uses the exists mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AntiJMulApply.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AntiJMulApply.lean#L54-L58

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

theorem GlobalTheory.SatakeWeyl.exists_mat (M : Matrix (Fin n) (Fin n) L) (hM : cT σ M * antiJ L n * M = antiJ L n) :
    ∃ g : GU σ n, mat g = M := by sorry
