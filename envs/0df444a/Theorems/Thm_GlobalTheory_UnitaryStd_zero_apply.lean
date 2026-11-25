-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryStd_zero_apply
-- name    : GlobalTheory.UnitaryStd.zero_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:06.745496+00:00
-- url     : https://prove2.me/theorems/1c697131-b43e-5eaf-a126-77e50fc9b929
-- title:
--   Unitary Std: zero apply
-- statement:
--   The Unitary Std construction uses the zero apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisApply.lean#L49-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisApply.lean#L49-L49

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

theorem GlobalTheory.UnitaryStd.zero_apply (i : Fin r) : (0 : Lat ρ g) i = 0 := by sorry
