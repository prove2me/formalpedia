-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FibreDensityLimit_ofReal_le_of_forall_compact
-- name    : GlobalTheory.CompanionTheory.FibreDensityLimit.ofReal_le_of_forall_compact
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:32.825797+00:00
-- url     : https://prove2.me/theorems/53041adb-1fa5-44fb-afc3-e36aa4283bc1
-- title:
--   Fibre Density Limit: of Real le of forall compact
-- statement:
--   The Fibre Density Limit construction uses the of Real le of forall compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DisintegrationInjectiveOpenMap.lean#L13-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DisintegrationInjectiveOpenMap.lean#L13-L40

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

theorem GlobalTheory.CompanionTheory.FibreDensityLimit.ofReal_le_of_forall_compact {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    {a b : X → ℝ} (ha : Continuous a) (hb : Continuous b) (c : ℝ)
    (h : ∀ A : Set X, IsCompact A → ∫⁻ s in A, ENNReal.ofReal (a s) ∂ν ≤
      ∫⁻ s in A, ENNReal.ofReal (b s) ∂ν + ENNReal.ofReal c * ν A) (s₀ : X) :
    ENNReal.ofReal (a s₀) ≤ ENNReal.ofReal (b s₀) + ENNReal.ofReal c := by sorry
