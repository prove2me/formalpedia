-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_measurable_partitionOfUnity_unitLogTranslates
-- name    : GlobalTheory.T.exists_measurable_partitionOfUnity_unitLogTranslates
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:37:39.013189+00:00
-- url     : https://prove2.me/theorems/709ed22f-85da-4ae8-b08f-14685899a936
-- title:
--   T: exists measurable partition Of Unity unit Log Translates
-- statement:
--   The T construction uses the exists measurable partition Of Unity unit Log Translates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMeasurablePartitionOfUnityUnitLogTranslateStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMeasurablePartitionOfUnityUnitLogTranslateStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMeasurablePartitionOfUnityUnitLogTranslate
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMeasurablePartitionOfUnityUnitLogTranslateStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_measurable_partitionOfUnity_unitLogTranslates : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∃ p : (I → ℝ) → ℝ, Measurable p ∧ (∀ y, 0 ≤ p y) ∧ (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) ∧ ∃ R : ℝ, ∀ y, p y ≠ 0 → ∀ i j, y i - y j ≤ R := by sorry
