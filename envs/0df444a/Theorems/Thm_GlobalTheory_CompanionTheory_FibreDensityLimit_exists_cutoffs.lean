-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FibreDensityLimit_exists_cutoffs
-- name    : GlobalTheory.CompanionTheory.FibreDensityLimit.exists_cutoffs
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:22.107693+00:00
-- url     : https://prove2.me/theorems/416ba91f-671f-4b7d-9977-f22c3372bb86
-- title:
--   Fibre Density Limit: exists cutoffs
-- statement:
--   The Fibre Density Limit construction uses the exists cutoffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DisintegrationInjectiveOpenMap.lean#L55-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DisintegrationInjectiveOpenMap.lean#L55-L106

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DisintegrationInjectiveOpenMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FibreDensityLimit
open Set

theorem GlobalTheory.CompanionTheory.FibreDensityLimit.exists_cutoffs {V : Type} [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [T2Space V] {U : Set V} (hU : IsOpen U) :
    ∃ χ : ℕ → V → ℝ, (∀ n, Continuous (χ n)) ∧ (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n, tsupport (χ n) ⊆ U) ∧ (∀ n v, 0 ≤ χ n v ∧ χ n v ≤ 1) ∧
      (∀ v, Monotone fun n => χ n v) ∧ ∀ v ∈ U, ∃ n, χ n v = 1 := by sorry
