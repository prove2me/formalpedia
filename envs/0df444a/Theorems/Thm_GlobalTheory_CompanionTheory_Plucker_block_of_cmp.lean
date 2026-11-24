-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_block_of_cmp
-- name    : GlobalTheory.CompanionTheory.Plucker.block_of_cmp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:08:23.268103+00:00
-- url     : https://prove2.me/theorems/22a4bde7-e15a-439e-b5d8-b6d0ba78810d
-- title:
--   Plucker: block of cmp
-- statement:
--   The Plucker construction uses the block of cmp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L98-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConvergenceGroupOfBlockDet.lean#L98-L156

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

theorem GlobalTheory.CompanionTheory.Plucker.block_of_cmp {E : Type} [Field E] (M : Matrix ι ι E) (t₀ : Sub ι m)
    (hu : IsUnit (cmp M : Matrix (Sub ι m) (Sub ι m) E).det) (h : ∀ t, t ≠ t₀ → cmp M t t₀ = 0) :
    ∀ r ∉ (t₀.1 : Set ι), ∀ c ∈ (t₀.1 : Set ι), M r c = 0 := by sorry
