-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cmp_conjTranspose
-- name    : GlobalTheory.CompanionTheory.Plucker.cmp_conjTranspose
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:06:54.800901+00:00
-- url     : https://prove2.me/theorems/212435fd-03cc-4511-b275-4d5bbbb609e8
-- title:
--   Plucker: cmp conj Transpose
-- statement:
--   The Plucker construction uses the cmp conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L64-L67

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.Plucker.cmp_conjTranspose (M : Matrix ι ι ℂ) :
    (cmp Mᴴ : Matrix (Sub ι m) (Sub ι m) ℂ) = (cmp M)ᴴ := by sorry
