-- Prove2me | Theorems.Thm_GlobalTheory_quad_eq_sum_symplDual
-- name    : GlobalTheory.quad_eq_sum_symplDual
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:15:09.934958+00:00
-- url     : https://prove2.me/theorems/af57cb5e-03d9-4e87-8c5b-a3ad3944056c
-- title:
--   Global Theory: quad eq sum sympl Dual
-- statement:
--   The Global Theory construction uses the quad eq sum sympl Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MetaplecticQuadraticOperatorEqSumSymplecticDual.lean#L8-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MetaplecticQuadraticOperatorEqSumSymplecticDual.lean#L8-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MetaplecticQuadraticOperatorEqSumSymplecticDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil
open GlobalTheory

theorem GlobalTheory.quad_eq_sum_symplDual (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ]
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ))
    (h : ∀ w, ∑ i, sympl (v i) w • u i = w) :
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i)) := by sorry
