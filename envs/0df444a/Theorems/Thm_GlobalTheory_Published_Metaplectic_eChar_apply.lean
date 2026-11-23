-- Prove2me | Theorems.Thm_GlobalTheory_Published_Metaplectic_eChar_apply
-- name    : GlobalTheory.Published.Metaplectic.eChar_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:32.726264+00:00
-- url     : https://prove2.me/theorems/338d60b9-c0af-4c40-bccc-7cfe38bde83a
-- title:
--   Metaplectic: e Char apply
-- statement:
--   The Metaplectic construction uses the e Char apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/MetaplecticRepresentation.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/MetaplecticRepresentation.lean#L17-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.Metaplectic
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.Published.Metaplectic.eChar_apply (x : ℝ) : eChar x = cexp (2 * π * x * I) := by sorry
