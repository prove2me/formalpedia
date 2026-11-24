-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealBox_image_box_bound
-- name    : GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.image_box_bound
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:21:13.906728+00:00
-- url     : https://prove2.me/theorems/cbaa3696-c3f8-4d09-a170-80597cefd1d4
-- title:
--   Real Box: image box bound
-- statement:
--   The Real Box construction uses the image box bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxVolumeBound.lean#L126-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxVolumeBound.lean#L126-L190

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxVolumeBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
variable {P ι : Type}

theorem GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.image_box_bound : ∀ (P ι : Type) [Fintype P] [Fintype ι] (A Pm : P → Matrix ι ι ℝ) (Di : (P → ℝ) → ℝ), 2 ≤ Fintype.card ι → Continuous Di → (∀ U : Set (P → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U, ENNReal.ofReal (gaussR Pm x) = ∫⁻ y in U, ENNReal.ofReal (Di y)) → ∃ C : ℝ≥0, ∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U → (volume : Measure (P → ι → ℝ)) (qR0 A ⁻¹' U ∩ boxR t) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ (Fintype.card ι - 2)) * volume U := by sorry
