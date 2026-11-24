-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_aesm_deriv
-- name    : GlobalTheory.CompanionTheory.HolMean.aesm_deriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:15.488399+00:00
-- url     : https://prove2.me/theorems/6a199c8a-8f9a-4a05-82cb-1c4c8a434876
-- title:
--   Hol Mean: aesm deriv
-- statement:
--   The Hol Mean construction uses the aesm deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AesmIteratedDerivReal.lean#L96-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AesmIteratedDerivReal.lean#L96-L125

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolMean
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {U : Set ℂ}

theorem GlobalTheory.CompanionTheory.HolMean.aesm_deriv (hU : IsOpen U) (G : ℂ → Ω → ℂ)
    (hd : ∀ ω, DifferentiableOn ℂ (fun z => G z ω) U) {z : ℂ} (hz : z ∈ U)
    (hm : ∀ x : ℝ, z + x ∈ U → AEStronglyMeasurable (G (z + x)) μ) :
    AEStronglyMeasurable (fun ω => deriv (fun w => G w ω) z) μ := by sorry
