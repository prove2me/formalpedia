-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryStd_cx_apply
-- name    : GlobalTheory.UnitaryStd.cx_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:45:31.076261+00:00
-- url     : https://prove2.me/theorems/dac54fdd-6178-4d04-8ad8-b8ff3db28632
-- title:
--   Unitary Std: cx apply
-- statement:
--   The Unitary Std construction uses the cx apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisApply.lean#L99-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisApply.lean#L99-L99

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

theorem GlobalTheory.UnitaryStd.cx_apply (x : Lat ρ g) (i : Fin r) : cx ρ g x i = ((x i).2, -(x i).1) := by sorry
