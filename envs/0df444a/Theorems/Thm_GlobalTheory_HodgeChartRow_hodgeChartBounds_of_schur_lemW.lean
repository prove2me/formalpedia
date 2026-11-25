-- Prove2me | Theorems.Thm_GlobalTheory_HodgeChartRow_hodgeChartBounds_of_schur_lemW
-- name    : GlobalTheory.HodgeChartRow.hodgeChartBounds_of_schur_lemW
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:07:51.361729+00:00
-- url     : https://prove2.me/theorems/407c11f7-1958-5ccc-bc02-02b36475e995
-- title:
--   Hodge Chart Row: hodge Chart Bounds of schur lem W
-- statement:
--   The Hodge Chart Row construction uses the hodge Chart Bounds of schur lem W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeChartBoundsOfSchurLemW.lean#L41-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeChartBoundsOfSchurLemW.lean#L41-L266

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodChartUniformConstantsHalfPolydiscStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionMatrixGramOperatorNormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernCurvatureFormSelfEqDualNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeChartBoundsOfSchurLemW
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
noncomputable section
open GlobalTheory GlobalTheory.HodgeChartRow

theorem GlobalTheory.HodgeChartRow.hodgeChartBounds_of_schur_lemW (hS : ∀ (k l : ℕ) (a bt : Matrix (Fin k) (Fin k) ℝ) (b : Matrix (Fin k) (Fin l) ℝ) (d : Matrix (Fin l) (Fin l) ℝ) (C₀ c₀ b₀ : ℝ), 0 ≤ C₀ → 0 < c₀ → 0 < b₀ → a.IsSymm → d.IsSymm → bt.IsSymm → (∀ x, |x ⬝ᵥ a.mulVec x| ≤ C₀ * (x ⬝ᵥ x)) → (∀ y, (b.mulVec y) ⬝ᵥ (b.mulVec y) ≤ C₀ ^ 2 * (y ⬝ᵥ y)) → (∀ y, c₀ * (y ⬝ᵥ y) ≤ y ⬝ᵥ d.mulVec y) → (∀ x, b₀ * (x ⬝ᵥ x) ≤ x ⬝ᵥ bt.mulVec x) → ∀ z : Fin k ⊕ Fin l → ℝ, ((1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀))⁻¹ * (z ⬝ᵥ z) ≤ z ⬝ᵥ (Matrix.fromBlocks (a + ((1 + C₀ + C₀ ^ 2 / c₀) / b₀) • bt) b b.transpose d).mulVec z) (hW : ∀ (g a : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (c C : ℝ), 0 < c → (∀ i, (B i).PosSemidef) → ∃ W : ℝ, ∀ (Y' : Matrix (Fin g) (Fin g) ℝ) (t : Fin a → ℝ), Y'.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y'.mulVec x) → (∀ x, x ⬝ᵥ Y'.mulVec x ≤ C * (x ⬝ᵥ x)) → (∀ i, 0 < t i) → ∀ i x, ‖(t i • ((Y' + ∑ l, t l • B l)⁻¹ * B i)).mulVec x‖ ≤ W * ‖x‖) : HodgeChartBounds := by sorry
