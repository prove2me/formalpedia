-- Prove2me | Theorems.Thm_GlobalTheory_HaarRightTranslate_modular_bdd_on_compact
-- name    : GlobalTheory.HaarRightTranslate.modular_bdd_on_compact
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:04.624198+00:00
-- url     : https://prove2.me/theorems/df04dd20-1f6e-4b15-a10a-6638cce6d4bb
-- title:
--   Haar Right Translate: modular bdd on compact
-- statement:
--   The Haar Right Translate construction uses the modular bdd on compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarLintegralMulRightLe.lean#L18-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarLintegralMulRightLe.lean#L18-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarLintegralMulRightLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.HaarRightTranslate
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

theorem GlobalTheory.HaarRightTranslate.modular_bdd_on_compact {V : Set H} (hV : IsCompact V) :
    ∃ M : ℝ≥0, ∀ v ∈ V, modularCharacterFun v ≤ M := by sorry
