-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_dRho_apply
-- name    : GlobalTheory.RealWeil.dRho_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:59.401542+00:00
-- url     : https://prove2.me/theorems/95ca940c-c6a4-41d1-aae8-8d11e82149b7
-- title:
--   Real Weil: d Rho apply
-- statement:
--   The Real Weil construction uses the d Rho apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean#L125-L129

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

theorem GlobalTheory.RealWeil.dRho_apply (w : l ⊕ l → ℝ) (f : Sch l) (x : EuclideanSpace ℝ l) :
    dRho w f x = fderiv ℝ f x (pPart w) + 2 * π * I * (⟪qPart w, x⟫ : ℝ) * f x := by sorry
