-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_mat_injective
-- name    : GlobalTheory.SatakeWeyl.mat_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:14:33.242815+00:00
-- url     : https://prove2.me/theorems/79297c34-d7c6-48fb-ba68-9b61eff52842
-- title:
--   Satake Weyl: mat injective
-- statement:
--   The Satake Weyl construction uses the mat injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AntiJMulApply.lean#L29-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AntiJMulApply.lean#L29-L29

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
omit [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.SatakeWeyl.mat_injective {g g' : GU σ n} (h : mat g = mat g') : g = g' := by sorry
