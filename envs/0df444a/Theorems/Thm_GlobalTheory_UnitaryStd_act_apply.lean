-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryStd_act_apply
-- name    : GlobalTheory.UnitaryStd.act_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:02.800504+00:00
-- url     : https://prove2.me/theorems/0216aad7-c167-48d6-9239-277790ac4494
-- title:
--   Unitary Std: act apply
-- statement:
--   The Unitary Std construction uses the act apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisApply.lean#L103-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisApply.lean#L103-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open GlobalTheory GlobalTheory.UnitaryStd
variable {r g : ℕ}
variable {E : Type} [Field E] [NumberField E] (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ)
variable {ρ g}
variable (ρ g)

theorem GlobalTheory.UnitaryStd.act_apply (a : 𝓞 E) (x : Lat ρ g) : act ρ g a x = a • x := by sorry
