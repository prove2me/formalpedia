-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_map_coe
-- name    : GlobalTheory.CompanionTheory.Plucker.map_coe
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:06:08.809043+00:00
-- url     : https://prove2.me/theorems/4e799897-d488-44ed-9e73-f28a42c31024
-- title:
--   Plucker: map coe
-- statement:
--   The Plucker construction uses the map coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L197-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L197-L198

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

theorem GlobalTheory.CompanionTheory.Plucker.map_coe (f : E →+* R) (δ : GL ι E) :
    ((Matrix.GeneralLinearGroup.map f δ : GL ι R) : Matrix ι ι R) = (δ : Matrix ι ι E).map f := by sorry
