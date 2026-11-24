-- Prove2me | Theorems.Thm_GlobalTheory_T_orthogonal_symplectic_fixes_siegel_point_i
-- name    : GlobalTheory.T.orthogonal_symplectic_fixes_siegel_point_i
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:55:59.174821+00:00
-- url     : https://prove2.me/theorems/ec6259d1-1807-4363-9f92-61eabbcfa2c1
-- title:
--   T: orthogonal symplectic fixes siegel point i
-- statement:
--   The T construction uses the orthogonal symplectic fixes siegel point i property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrthogonalSymplecticFixesSiegelPointIStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrthogonalSymplecticFixesSiegelPointIStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrthogonalSymplecticFixesSiegelPointI
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrthogonalSymplecticFixesSiegelPointIStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.orthogonal_symplectic_fixes_siegel_point_i : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → sᵀ * s = 1 → P.det ≠ 0 → GlobalTheory.Published.Metaplectic.holPart s = P ∧ ∀ x : l → ℝ, cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by sorry
