-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_mul_J_symm
-- name    : GlobalTheory.RealWeil.mul_J_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:35.161802+00:00
-- url     : https://prove2.me/theorems/96d9047e-6ef6-4f27-8d3d-938b69428fbb
-- title:
--   Real Weil: mul J symm
-- statement:
--   The Real Weil construction uses the mul J symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean#L195-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean#L195-L203

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

theorem GlobalTheory.RealWeil.mul_J_symm {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) :
    (X * Matrix.J l ℝ)ᵀ = X * Matrix.J l ℝ := by sorry
