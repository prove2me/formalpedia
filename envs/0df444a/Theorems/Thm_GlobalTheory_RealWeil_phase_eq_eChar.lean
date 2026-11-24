-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_phase_eq_eChar
-- name    : GlobalTheory.RealWeil.phase_eq_eChar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:59.808815+00:00
-- url     : https://prove2.me/theorems/aca4b9b7-75d1-42ba-bcee-c13eb98f0fd0
-- title:
--   Real Weil: phase eq e Char
-- statement:
--   The Real Weil construction uses the phase eq e Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSchwartzTranslate.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSchwartzTranslate.lean#L14-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]

theorem GlobalTheory.RealWeil.phase_eq_eChar (w : l ⊕ l → ℝ) (x : EuclideanSpace ℝ l) :
    phase w x = GlobalTheory.Published.Metaplectic.eChar (⟪qPart w, x⟫ + ⟪pPart w, qPart w⟫ / 2) := by sorry
