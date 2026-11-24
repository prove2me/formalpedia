-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_continuous_qPart
-- name    : GlobalTheory.RealWeil.continuous_qPart
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:16:22.579479+00:00
-- url     : https://prove2.me/theorems/c0da5d45-d0ad-40bb-bcfc-fc91c8bb568e
-- title:
--   Real Weil: continuous q Part
-- statement:
--   The Real Weil construction uses the continuous q Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousRhoApply.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousRhoApply.lean#L20-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousRhoApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex
open scoped Matrix Real RealInnerProductSpace InnerProductSpace
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
omit [Fintype l]

theorem GlobalTheory.RealWeil.continuous_qPart : Continuous (qPart : (l ⊕ l → ℝ) → EuclideanSpace ℝ l) := by sorry
