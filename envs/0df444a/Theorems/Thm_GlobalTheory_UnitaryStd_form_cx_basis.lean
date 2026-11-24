-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryStd_form_cx_basis
-- name    : GlobalTheory.UnitaryStd.form_cx_basis
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:45:39.302606+00:00
-- url     : https://prove2.me/theorems/1bf129da-b92c-49e3-9f26-c0c17100d192
-- title:
--   Unitary Std: form cx basis
-- statement:
--   The Unitary Std construction uses the form cx basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryStandardLatticeFormComplexStructureBaseCh.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryStandardLatticeFormComplexStructureBaseCh.lean#L19-L25

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

theorem GlobalTheory.UnitaryStd.form_cx_basis (S : Matrix (Fin r) (Fin r) ℤ) (p q : Fin r × (Fin g ⊕ Fin g)) :
    form ρ g S (cx ρ g (basis ρ g p)) (basis ρ g q) = if p.2 = q.2 then S p.1 q.1 else 0 := by sorry
