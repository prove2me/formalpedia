-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_norm_det_blk
-- name    : GlobalTheory.CompanionTheory.RgEis.norm_det_blk
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:18.152699+00:00
-- url     : https://prove2.me/theorems/6d7ea2f1-1a85-4a00-8992-7979d1d5c2d0
-- title:
--   Rg Eis: norm det blk
-- statement:
--   The Rg Eis construction uses the norm det blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L140-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L140-L152

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw
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
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
variable {E : Type} [Field E]
open Classical

theorem GlobalTheory.CompanionTheory.RgEis.norm_det_blk (M : Matrix ι ι ℂ) (hM : M ∈ Matrix.unitaryGroup ι ℂ) (s : Set ι)
    (h0 : ∀ r, r ∉ s → ∀ c ∈ s, M r c = 0) :
    ‖(M.submatrix (Subtype.val : s → ι) Subtype.val).det‖ = 1 := by sorry
