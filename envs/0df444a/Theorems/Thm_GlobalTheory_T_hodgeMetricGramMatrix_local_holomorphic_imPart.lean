-- Prove2me | Theorems.Thm_GlobalTheory_T_hodgeMetricGramMatrix_local_holomorphic_imPart
-- name    : GlobalTheory.T.hodgeMetricGramMatrix_local_holomorphic_imPart
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:56:44.810251+00:00
-- url     : https://prove2.me/theorems/669db13a-d027-42dc-bd70-310cb0fbea4b
-- title:
--   T: hodge Metric Gram Matrix local holomorphic im Part
-- statement:
--   The T construction uses the hodge Metric Gram Matrix local holomorphic im Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPartStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPartStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPart
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPartStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hodgeMetricGramMatrix_local_holomorphic_imPart : ∀ (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), IsPeriodChart rk τ₀ B → ∀ z ∈ punctured ha 1, MContDiffAt ∞ (hodgeGram ha τ₀ B) z ∧ (∀ ξ, mdel (hodgeGram ha τ₀ B) z ξ = (1 / (2 * Complex.I)) • ((Matrix.of fun j k => fderiv ℂ (fun x => τ₀ x j k) z ξ) + ∑ i, (ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))) • ((B i).map (Int.cast : ℤ → ℝ)).map Complex.ofReal)) ∧ ∀ ξ η, mddbar (hodgeGram ha τ₀ B) z ξ η = 0 := by sorry
