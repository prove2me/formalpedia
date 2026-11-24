-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_conv_of_line
-- name    : GlobalTheory.CompanionTheory.Plucker.conv_of_line
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:05:36.666016+00:00
-- url     : https://prove2.me/theorems/cf2e747b-be04-4ff4-b09b-7727de712657
-- title:
--   Plucker: conv of line
-- statement:
--   The Plucker construction uses the conv of line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L284-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L284-L323

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Plucker
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]
  {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]

theorem GlobalTheory.CompanionTheory.Plucker.conv_of_line (hB : BdetLaw) (hE : ExtLaw) (A : Ad E R) (hA : A.GoodL) (t₀ : Sub ι m) (x : ℝ)
    (hx : Conv (A.ratGL (Sub ι m)) (stab R ({t₀} : Set (Sub ι m))) fun g => x * A.htGL ({t₀} : Set (Sub ι m)) g) :
    Conv (A.ratGL ι) (stab R (t₀.1 : Set ι)) fun g => x * A.htGL (t₀.1 : Set ι) g := by sorry
