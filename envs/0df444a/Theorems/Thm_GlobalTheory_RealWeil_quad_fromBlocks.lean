-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_quad_fromBlocks
-- name    : GlobalTheory.RealWeil.quad_fromBlocks
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:24.275801+00:00
-- url     : https://prove2.me/theorems/7b89f8a4-c23c-4b1c-9713-7ee5fc3a095b
-- title:
--   Real Weil: quad from Blocks
-- statement:
--   The Real Weil construction uses the quad from Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean#L282-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RealMetaplecticRepresentation.lean#L282-L343

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

theorem GlobalTheory.RealWeil.quad_fromBlocks {A B C D : Matrix l l ℝ} (hX : fromBlocks A B C D ∈ LieAlgebra.Symplectic.sp l ℝ)
    (f : Sch l) (x : EuclideanSpace ℝ l) :
    quad (fromBlocks A B C D) f x =
      (4 * π * I : ℂ)⁻¹ * ∑ j, ∑ k, (B j k : ℂ) * (∂_{(EuclideanSpace.single j 1 : EuclideanSpace ℝ l)}
          (∂_{(EuclideanSpace.single k 1 : EuclideanSpace ℝ l)} f)) x
        - ∑ j, ∑ k, (A j k : ℂ) * x k * (∂_{(EuclideanSpace.single j 1 : EuclideanSpace ℝ l)} f) x
        - (A.trace : ℝ) / 2 * f x - π * I * ∑ j, ∑ k, (C j k : ℂ) * x j * x k * f x := by sorry
