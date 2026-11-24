-- Prove2me | Theorems.Thm_GlobalTheory_Published_Metaplectic_act_fromBlocks
-- name    : GlobalTheory.Published.Metaplectic.act_fromBlocks
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:56:17.252528+00:00
-- url     : https://prove2.me/theorems/de81725d-c434-45bd-b2cd-5752a8ebff9c
-- title:
--   Metaplectic: act from Blocks
-- statement:
--   The Metaplectic construction uses the act from Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/MetaplecticRepresentation.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/MetaplecticRepresentation.lean#L83-L85

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

theorem GlobalTheory.Published.Metaplectic.act_fromBlocks (A B C D : Matrix ι ι ℝ) (p q : ι → ℝ) :
    act (fromBlocks A B C D) (p, q) = (A *ᵥ p + B *ᵥ q, C *ᵥ p + D *ᵥ q) := by sorry
