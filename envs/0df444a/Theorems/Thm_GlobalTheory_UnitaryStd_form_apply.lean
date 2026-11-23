-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryStd_form_apply
-- name    : GlobalTheory.UnitaryStd.form_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:16.868694+00:00
-- url     : https://prove2.me/theorems/f95ba289-f93f-4112-b696-76a1613a5f67
-- title:
--   Unitary Std: form apply
-- statement:
--   The Unitary Std construction uses the form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisApply.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisApply.lean#L83-L84

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

theorem GlobalTheory.UnitaryStd.form_apply (S : Matrix (Fin r) (Fin r) ℤ) (x y : Lat ρ g) :
    form ρ g S x y = ∑ i, ∑ j, S i j * ((x i).1 ⬝ᵥ (y j).2 - (x i).2 ⬝ᵥ (y j).1) := by sorry
