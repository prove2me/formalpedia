-- Prove2me | Theorems.Thm_GlobalTheory_PoincareBounds_poincareGram_eq
-- name    : GlobalTheory.PoincareBounds.poincareGram_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:26.90482+00:00
-- url     : https://prove2.me/theorems/d6cbcfc3-71c7-43ce-aee4-a5475cf21d75
-- title:
--   Poincare Bounds: poincare Gram eq
-- statement:
--   The Poincare Bounds construction uses the poincare Gram eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PoincareMetricPuncturedPolydiscBounds.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PoincareMetricPuncturedPolydiscBounds.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.PoincareBounds

theorem GlobalTheory.PoincareBounds.poincareGram_eq {n : ℕ} (a : ℕ) (z : Fin n → ℂ) :
    poincareGram a z = diagonal fun k => ((pdiag a z k : ℝ) : ℂ) := by sorry
