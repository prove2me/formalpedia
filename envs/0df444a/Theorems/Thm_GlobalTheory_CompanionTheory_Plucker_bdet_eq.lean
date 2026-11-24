-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_bdet_eq
-- name    : GlobalTheory.CompanionTheory.Plucker.bdet_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:06:40.229885+00:00
-- url     : https://prove2.me/theorems/c06049e3-b3f3-4e13-8bc8-9b17af349c96
-- title:
--   Plucker: bdet eq
-- statement:
--   The Plucker construction uses the bdet eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L240-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L240-L253

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

theorem GlobalTheory.CompanionTheory.Plucker.bdet_eq {κ : Type} [Fintype κ] [DecidableEq κ] {s : Set ι} {s' : Set κ} {g : GL ι R} {g' : GL κ R}
    (h : ∀ [Fintype s] [DecidableEq s] [Fintype s'] [DecidableEq s'],
      ((g : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det =
      ((g' : Matrix κ κ R).submatrix (Subtype.val : s' → κ) Subtype.val).det) : bdet s g = bdet s' g' := by sorry
