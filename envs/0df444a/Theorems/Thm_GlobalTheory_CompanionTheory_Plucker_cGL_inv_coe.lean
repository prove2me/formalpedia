-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cGL_inv_coe
-- name    : GlobalTheory.CompanionTheory.Plucker.cGL_inv_coe
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:08:42.103577+00:00
-- url     : https://prove2.me/theorems/5abd2460-d611-4a19-9b6a-9daa64fbe740
-- title:
--   Plucker: c GL inv coe
-- statement:
--   The Plucker construction uses the c GL inv coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L178-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L178-L181

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
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]

theorem GlobalTheory.CompanionTheory.Plucker.cGL_inv_coe (g : GL ι R) :
    (((cGL m g)⁻¹ : GL (Sub ι m) R) : Matrix (Sub ι m) (Sub ι m) R) = cmp ((g⁻¹ : GL ι R) : Matrix ι ι R) := by sorry
