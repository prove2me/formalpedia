-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_mat_inv_apply
-- name    : GlobalTheory.SatakeWeyl.mat_inv_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:09:46.275662+00:00
-- url     : https://prove2.me/theorems/6c5ffcc7-aa89-40ca-b9e7-08b277573a88
-- title:
--   Satake Weyl: mat inv apply
-- statement:
--   The Satake Weyl construction uses the mat inv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AntiJMulApply.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AntiJMulApply.lean#L46-L52

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

theorem GlobalTheory.SatakeWeyl.mat_inv_apply (g : GU σ n) (i j : Fin n) : mat g⁻¹ i j = σ (mat g j.rev i.rev) := by sorry
