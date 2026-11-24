-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_hasDerivAt_rhoFun
-- name    : GlobalTheory.RealWeil.hasDerivAt_rhoFun
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:08.189027+00:00
-- url     : https://prove2.me/theorems/26f3c42e-713f-4e65-bc40-0fc0de2742f3
-- title:
--   Real Weil: has Deriv At rho Fun
-- statement:
--   The Real Weil construction uses the has Deriv At rho Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean#L131-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean#L131-L149

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

theorem GlobalTheory.RealWeil.hasDerivAt_rhoFun (w : l ⊕ l → ℝ) (f : Sch l) (x : EuclideanSpace ℝ l) :
    HasDerivAt (fun t : ℝ => rhoFun (t • w) f x) (dRho w f x) 0 := by sorry
