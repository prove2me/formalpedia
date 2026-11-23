-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_measurePreserving_cons
-- name    : GlobalTheory.GLFirstColumn.measurePreserving_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:27.501808+00:00
-- url     : https://prove2.me/theorems/cb97b900-1ce1-43a3-a155-a533fc6d7dff
-- title:
--   GLFirst Column: measure Preserving cons
-- statement:
--   The GLFirst Column construction uses the measure Preserving cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L267-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L267-L276

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.GLFirstColumn

theorem GlobalTheory.GLFirstColumn.measurePreserving_cons (X : Type) [MeasureSpace X] [SigmaFinite (volume : Measure X)]
    (n : ℕ) : MeasurePreserving
      (fun p : X × (Fin n → X) => (Fin.cons p.1 p.2 : Fin (n + 1) → X)) volume volume := by sorry
