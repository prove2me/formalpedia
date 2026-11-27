-- Prove2me | Theorems.Thm_GlobalTheory_T_unitaryStandardLattice_form_complexStructure_baseChange_pos
-- name    : GlobalTheory.T.unitaryStandardLattice_form_complexStructure_baseChange_pos
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:40:48.290292+00:00
-- url     : https://prove2.me/theorems/d97e37b8-00b3-4343-8f0e-a2afe393ebf5
-- title:
--   T: unitary Standard Lattice form complex Structure base Change pos
-- statement:
--   The T construction uses the unitary Standard Lattice form complex Structure base Change pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryStandardLatticeFormComplexStructureBaseChStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryStandardLatticeFormComplexStructureBaseChStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeFormComplexStructureBaseCh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeFormComplexStructureBaseChStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.unitaryStandardLattice_form_complexStructure_baseChange_pos : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ), (S.map (Int.cast : ℤ → ℝ)).PosDef → ∀ x : ℝ ⊗[ℤ] GlobalTheory.UnitaryStd.Lat ρ g, x ≠ 0 → 0 < (GlobalTheory.UnitaryStd.form ρ g S).baseChange ℝ ((GlobalTheory.UnitaryStd.cx ρ g).baseChange ℝ x) x := by sorry
