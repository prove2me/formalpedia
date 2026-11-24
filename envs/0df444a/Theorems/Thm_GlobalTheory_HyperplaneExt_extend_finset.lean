-- Prove2me | Theorems.Thm_GlobalTheory_HyperplaneExt_extend_finset
-- name    : GlobalTheory.HyperplaneExt.extend_finset
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:13:40.993857+00:00
-- url     : https://prove2.me/theorems/0ed6c9c9-c399-492b-8f9a-9166a98949e5
-- title:
--   Hyperplane Ext: extend finset
-- statement:
--   The Hyperplane Ext construction uses the extend finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExtensionAcrossCoordinateHyperplanes.lean#L31-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExtensionAcrossCoordinateHyperplanes.lean#L31-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExtensionAcrossZeroOfExpTwoPiIBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocallyBoundedOffCoordinateHyperplanesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannExtensionCoordinateHyperplaneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExtensionAcrossCoordinateHyperplanes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
open GlobalTheory GlobalTheory.HyperplaneExt

theorem GlobalTheory.HyperplaneExt.extend_finset (hR : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z) :
    ∀ (n : ℕ) (s : Finset (Fin n)) (W : Set (Fin n → ℂ)) (Φ : (Fin n → ℂ) → ℂ), IsOpen W →
      DifferentiableOn ℂ Φ {z | z ∈ W ∧ ∀ k ∈ s, z k ≠ 0} →
      (∀ z₀ ∈ W, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ W → (∀ k ∈ s, z k ≠ 0) → ‖Φ z‖ ≤ M) →
      ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧ ∀ z ∈ W, (∀ k ∈ s, z k ≠ 0) → F z = Φ z := by sorry
