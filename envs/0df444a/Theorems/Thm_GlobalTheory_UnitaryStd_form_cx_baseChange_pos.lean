-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryStd_form_cx_baseChange_pos
-- name    : GlobalTheory.UnitaryStd.form_cx_baseChange_pos
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:46:02.307917+00:00
-- url     : https://prove2.me/theorems/4549a024-532b-4292-8cc8-33fc223ca493
-- title:
--   Unitary Std: form cx base Change pos
-- statement:
--   The Unitary Std construction uses the form cx base Change pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryStandardLatticeFormComplexStructureBaseCh.lean#L27-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryStandardLatticeFormComplexStructureBaseCh.lean#L27-L64

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

theorem GlobalTheory.UnitaryStd.form_cx_baseChange_pos (S : Matrix (Fin r) (Fin r) ℤ) (hS : (S.map (Int.cast : ℤ → ℝ)).PosDef)
    (x : ℝ ⊗[ℤ] Lat ρ g) (hx : x ≠ 0) :
    0 < (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x := by sorry
