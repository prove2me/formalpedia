-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_qPart_smul
-- name    : GlobalTheory.RealWeil.qPart_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:31.740797+00:00
-- url     : https://prove2.me/theorems/9830fdc1-4371-4589-bde6-a3c702197bdf
-- title:
--   Real Weil: q Part smul
-- statement:
--   The Real Weil construction uses the q Part smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean#L38-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean#L38-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
omit [Fintype l]

theorem GlobalTheory.RealWeil.qPart_smul (t : ℝ) (w : l ⊕ l → ℝ) : qPart (t • w) = t • qPart w := by sorry
