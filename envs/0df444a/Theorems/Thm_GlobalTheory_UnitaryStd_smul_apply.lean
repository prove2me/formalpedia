-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryStd_smul_apply
-- name    : GlobalTheory.UnitaryStd.smul_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:45:13.005805+00:00
-- url     : https://prove2.me/theorems/d1304751-2df8-4065-85c2-bf263bafca2c
-- title:
--   Unitary Std: smul apply
-- statement:
--   The Unitary Std construction uses the smul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisApply.lean#L41-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisApply.lean#L41-L41

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

theorem GlobalTheory.UnitaryStd.smul_apply (a : 𝓞 E) (x : Lat ρ g) (i : Fin r) : (a • x) i = ∑ j, ρ a i j • x j := by sorry
