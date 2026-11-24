-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryStd_neg_apply
-- name    : GlobalTheory.UnitaryStd.neg_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:45:28.666506+00:00
-- url     : https://prove2.me/theorems/0877d302-b839-42e7-bcb7-192ed2df3ab6
-- title:
--   Unitary Std: neg apply
-- statement:
--   The Unitary Std construction uses the neg apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisApply.lean#L47-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisApply.lean#L47-L47

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

theorem GlobalTheory.UnitaryStd.neg_apply (x : Lat ρ g) (i : Fin r) : (-x) i = -x i := by sorry
