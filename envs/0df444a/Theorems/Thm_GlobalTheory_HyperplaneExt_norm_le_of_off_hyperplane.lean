-- Prove2me | Theorems.Thm_GlobalTheory_HyperplaneExt_norm_le_of_off_hyperplane
-- name    : GlobalTheory.HyperplaneExt.norm_le_of_off_hyperplane
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:13:51.968023+00:00
-- url     : https://prove2.me/theorems/692dc17d-32e0-4580-9c7a-1740e65891ea
-- title:
--   Hyperplane Ext: norm le of off hyperplane
-- statement:
--   The Hyperplane Ext construction uses the norm le of off hyperplane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExtensionAcrossCoordinateHyperplanes.lean#L10-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExtensionAcrossCoordinateHyperplanes.lean#L10-L29

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

theorem GlobalTheory.HyperplaneExt.norm_le_of_off_hyperplane {n : ℕ} {U V : Set (Fin n → ℂ)} {k : Fin n} {F : (Fin n → ℂ) → ℂ} {M : ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContinuousOn F U)
    (hb : ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖F z‖ ≤ M) : ∀ z ∈ V, z ∈ U → ‖F z‖ ≤ M := by sorry
