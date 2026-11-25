-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_imagQuadratic_subfield_of_toricCMFieldData
-- name    : GlobalTheory.T.exists_imagQuadratic_subfield_of_toricCMFieldData
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:30:10.759138+00:00
-- url     : https://prove2.me/theorems/f518a865-77f6-4fc4-a4c9-62fc15409008
-- title:
--   T: exists imag Quadratic subfield of toric CMField Data
-- statement:
--   The T construction uses the exists imag Quadratic subfield of toric CMField Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsImagQuadraticSubfieldOfToricCMFieldDataStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsImagQuadraticSubfieldOfToricCMFieldDataStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsImagQuadraticSubfieldOfToricCMFieldData
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_VpBounds
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsImagQuadraticSubfieldOfToricCMFieldDataStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_imagQuadratic_subfield_of_toricCMFieldData : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d : ℕ) (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → d % 4 = 3 → ∀ (Λ : PeriodPair), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → ∃ K : IntermediateField ℚ E, Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ ∃ φK : K →+* ℂ, (∀ i, (φ i).comp (algebraMap K E) = φK) ∧ (starRingEnd ℂ).comp φK ≠ φK ∧ IsLatOf φK 1 Λ := by sorry
