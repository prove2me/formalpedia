-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_sympl_single
-- name    : GlobalTheory.RealWeil.sympl_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:48.262722+00:00
-- url     : https://prove2.me/theorems/d2e874d3-00bb-476b-bf05-272d85504d60
-- title:
--   Real Weil: sympl single
-- statement:
--   The Real Weil construction uses the sympl single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean#L213-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean#L213-L215

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
variable [DecidableEq l]

theorem GlobalTheory.RealWeil.sympl_single (b : l ⊕ l) (u : l ⊕ l → ℝ) : sympl (Pi.single b 1) u = -(Matrix.J l ℝ *ᵥ u) b := by sorry
