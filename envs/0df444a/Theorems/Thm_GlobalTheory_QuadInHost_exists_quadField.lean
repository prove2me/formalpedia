-- Prove2me | Theorems.Thm_GlobalTheory_QuadInHost_exists_quadField
-- name    : GlobalTheory.QuadInHost.exists_quadField
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:14:17.47995+00:00
-- url     : https://prove2.me/theorems/13af331a-46f5-4253-8b2a-9b21655267b5
-- title:
--   Quad In Host: exists quad Field
-- statement:
--   The Quad In Host construction uses the exists quad Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsImagQuadraticSubfieldOfToricCMFieldData.lean#L10-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsImagQuadraticSubfieldOfToricCMFieldData.lean#L10-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_VpBounds
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsImagQuadraticSubfieldOfToricCMFieldData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped IntermediateField
open GlobalTheory GlobalTheory.QuadInHost

theorem GlobalTheory.QuadInHost.exists_quadField : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d : ℕ) (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → d % 4 = 3 → ∀ (Λ : PeriodPair), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → ∃ K : IntermediateField ℚ E, Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ ∃ φK : K →+* ℂ, (∀ i, (φ i).comp (algebraMap K E) = φK) ∧ (starRingEnd ℂ).comp φK ≠ φK ∧ IsLatOf φK 1 Λ := by sorry
