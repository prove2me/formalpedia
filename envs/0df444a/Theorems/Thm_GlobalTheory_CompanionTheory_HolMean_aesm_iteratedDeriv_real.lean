-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_aesm_iteratedDeriv_real
-- name    : GlobalTheory.CompanionTheory.HolMean.aesm_iteratedDeriv_real
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:38.363091+00:00
-- url     : https://prove2.me/theorems/8d1a9bb5-a35e-42e0-a85e-49577667b679
-- title:
--   Hol Mean: aesm iterated Deriv real
-- statement:
--   The Hol Mean construction uses the aesm iterated Deriv real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AesmIteratedDerivReal.lean#L127-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AesmIteratedDerivReal.lean#L127-L148

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

theorem GlobalTheory.CompanionTheory.HolMean.aesm_iteratedDeriv_real (hU : IsOpen U) (n : ℕ) : ∀ G : ℂ → Ω → ℂ,
    (∀ ω, DifferentiableOn ℂ (fun z => G z ω) U) →
    (∀ t : ℝ, (t : ℂ) ∈ U → AEStronglyMeasurable (G t) μ) →
    ∀ t : ℝ, (t : ℂ) ∈ U → AEStronglyMeasurable (fun ω => iteratedDeriv n (fun w => G w ω) t) μ := by sorry
