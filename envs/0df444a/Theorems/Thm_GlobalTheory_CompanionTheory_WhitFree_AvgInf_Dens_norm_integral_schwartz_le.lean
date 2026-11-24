-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WhitFree_AvgInf_Dens_norm_integral_schwartz_le
-- name    : GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.norm_integral_schwartz_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:24:16.174573+00:00
-- url     : https://prove2.me/theorems/6eb7c8ce-4b3e-475c-81a4-fcaaea25f014
-- title:
--   Dens: norm integral schwartz le
-- statement:
--   The Dens construction uses the norm integral schwartz le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DensityOfFourierPairingIntegrable.lean#L57-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DensityOfFourierPairingIntegrable.lean#L57-L66

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityOfFourierPairingIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Complex SchwartzMap FourierTransform
open scoped ENNReal NNReal RealInnerProductSpace Topology ContDiff Manifold
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WhitFree.AvgInf GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.norm_integral_schwartz_le (m : Measure V) [IsFiniteMeasure m] (hi : Integrable (chf m)) (g : 𝓢(V, ℂ)) :
    ‖∫ y, g y ∂m‖ ≤ (∫ x, ‖g x‖) * ∫ ξ, ‖chf m ξ‖ := by sorry
