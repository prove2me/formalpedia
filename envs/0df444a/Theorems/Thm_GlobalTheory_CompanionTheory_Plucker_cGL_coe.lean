-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cGL_coe
-- name    : GlobalTheory.CompanionTheory.Plucker.cGL_coe
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:06:32.493129+00:00
-- url     : https://prove2.me/theorems/9fca3ef3-dde5-4370-8cc6-a534cdba8689
-- title:
--   Plucker: c GL coe
-- statement:
--   The Plucker construction uses the c GL coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L166-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L166-L166

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

theorem GlobalTheory.CompanionTheory.Plucker.cGL_coe (g : GL ι R) : ((cGL m g : GL (Sub ι m) R) : Matrix (Sub ι m) (Sub ι m) R) = cmp (g : Matrix ι ι R) := by sorry
