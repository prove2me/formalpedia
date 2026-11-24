-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_det_submatrix_eq_zero
-- name    : GlobalTheory.CompanionTheory.Plucker.det_submatrix_eq_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:05:49.696788+00:00
-- url     : https://prove2.me/theorems/b7b54202-91c4-4dab-8bc2-d38565e9337f
-- title:
--   Plucker: det submatrix eq zero
-- statement:
--   The Plucker construction uses the det submatrix eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L85-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L85-L96

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

theorem GlobalTheory.CompanionTheory.Plucker.det_submatrix_eq_zero (M : Matrix ι ι R) (t u : Sub ι m) (f : m → ι) (hf : Function.Injective f)
    (hr : ∀ a, f a ∈ t.1) (h0 : cmp M t u = 0) : (M.submatrix f (en u)).det = 0 := by sorry
