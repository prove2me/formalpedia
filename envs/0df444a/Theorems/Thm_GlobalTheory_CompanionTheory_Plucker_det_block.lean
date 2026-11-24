-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_det_block
-- name    : GlobalTheory.CompanionTheory.Plucker.det_block
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:05:43.185517+00:00
-- url     : https://prove2.me/theorems/c743bda6-1f00-42e1-b288-f5dd5a76c9f7
-- title:
--   Plucker: det block
-- statement:
--   The Plucker construction uses the det block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L73-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L73-L83

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

theorem GlobalTheory.CompanionTheory.Plucker.det_block (t₀ : Sub ι m) (s : Set ι) (hs : s = (t₀.1 : Set ι)) [Fintype s] [DecidableEq s]
    (M : Matrix ι ι R) : (M.submatrix (Subtype.val : s → ι) Subtype.val).det = cmp M t₀ t₀ := by sorry
