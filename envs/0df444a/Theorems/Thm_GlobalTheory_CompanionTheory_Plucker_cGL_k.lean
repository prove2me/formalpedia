-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cGL_k
-- name    : GlobalTheory.CompanionTheory.Plucker.cGL_k
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:06:34.147747+00:00
-- url     : https://prove2.me/theorems/f65f604e-5178-44d1-b889-a78bb391f851
-- title:
--   Plucker: c GL k
-- statement:
--   The Plucker construction uses the c GL k property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L231-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L231-L238

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

theorem GlobalTheory.CompanionTheory.Plucker.cGL_k (A : Ad E R) {k : GL ι R} (hk : k ∈ A.kGL ι) : cGL m k ∈ A.kGL (Sub ι m) := by sorry
