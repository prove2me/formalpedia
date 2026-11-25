-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WhitFree_AvgInf_Dens_pairC_nondeg
-- name    : GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.pairC_nondeg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:59.557926+00:00
-- url     : https://prove2.me/theorems/a893b8c5-71c2-417b-b3f4-9f9114fb00c3
-- title:
--   Dens: pair C nondeg
-- statement:
--   The Dens construction uses the pair C nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DensityOfFourierPairingIntegrable.lean#L320-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DensityOfFourierPairingIntegrable.lean#L320-L337

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
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
variable {W : Type} [Fintype W]

theorem GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.pairC_nondeg {n : ℕ} {c : W → ℝ} (hc : ∀ w, c w ≠ 0) (u : W → hermC n)
    (h : ∀ v, pairC n c u v = 0) : u = 0 := by sorry
