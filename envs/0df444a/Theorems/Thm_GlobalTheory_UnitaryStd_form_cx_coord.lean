-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryStd_form_cx_coord
-- name    : GlobalTheory.UnitaryStd.form_cx_coord
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:45:37.923092+00:00
-- url     : https://prove2.me/theorems/7f4b12cf-6e07-408a-ac09-3a4cdf87ee7a
-- title:
--   Unitary Std: form cx coord
-- statement:
--   The Unitary Std construction uses the form cx coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryStandardLatticeFormComplexStructureBaseCh.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryStandardLatticeFormComplexStructureBaseCh.lean#L10-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeFormComplexStructureBaseCh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.UnitaryStd
variable {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ)

theorem GlobalTheory.UnitaryStd.form_cx_coord (S : Matrix (Fin r) (Fin r) ℤ) (y z : Lat ρ g) :
    form ρ g S (cx ρ g y) z = ∑ i, ∑ j, S i j *
      ∑ α : Fin g ⊕ Fin g, (basis ρ g).repr y (i, α) * (basis ρ g).repr z (j, α) := by sorry
