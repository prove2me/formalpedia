-- Prove2me | Theorems.Thm_GlobalTheory_DoublingLength_exists_small
-- name    : GlobalTheory.DoublingLength.exists_small
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:52:29.921985+00:00
-- url     : https://prove2.me/theorems/7cf2e5b5-b3d9-4ebb-abe4-1e53dfa1a999
-- title:
--   Doubling Length: exists small
-- statement:
--   The Doubling Length construction uses the exists small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumSphericalFunctionDoublingLength.lean#L186-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumSphericalFunctionDoublingLength.lean#L186-L208

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunctionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.DoublingLength
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem GlobalTheory.DoublingLength.exists_small (q : ℝ) (hq0 : 0 ≤ q) (γ : Fin n → ℂ) : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 ≤ x → x < δ → ∀ i : Fin n,
    q ^ (n - 1 - (i : ℕ)) * ‖γ i‖ * x < 1 ∧ q ^ (i : ℕ) * ‖γ i‖⁻¹ * x < 1 ∧ q ^ (i : ℕ) * x ^ 2 < 1 := by sorry
