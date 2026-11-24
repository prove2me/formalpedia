-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_isUnit_det_blk
-- name    : GlobalTheory.CompanionTheory.RgEis.isUnit_det_blk
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:27.525872+00:00
-- url     : https://prove2.me/theorems/ac16a708-524f-4d3a-ab2c-cc5426db93c3
-- title:
--   Rg Eis: is Unit det blk
-- statement:
--   The Rg Eis construction uses the is Unit det blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L45-L47

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
open Classical

theorem GlobalTheory.CompanionTheory.RgEis.isUnit_det_blk (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) :
    IsUnit ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det := by sorry
