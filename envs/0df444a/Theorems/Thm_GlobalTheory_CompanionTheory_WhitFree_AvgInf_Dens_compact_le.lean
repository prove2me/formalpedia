-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WhitFree_AvgInf_Dens_compact_le
-- name    : GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.compact_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:24:15.856221+00:00
-- url     : https://prove2.me/theorems/f6b495fa-5734-4da8-82b4-ba7abf727188
-- title:
--   Dens: compact le
-- statement:
--   The Dens construction uses the compact le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DensityOfFourierPairingIntegrable.lean#L68-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DensityOfFourierPairingIntegrable.lean#L68-L119

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

theorem GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.compact_le (m : Measure V) [IsFiniteMeasure m] (hi : Integrable (chf m)) {K U : Set V}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    m K ≤ ENNReal.ofReal (∫ ξ, ‖chf m ξ‖) * volume U := by sorry
