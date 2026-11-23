-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_blk_mul
-- name    : GlobalTheory.CompanionTheory.RgEis.blk_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:59.224176+00:00
-- url     : https://prove2.me/theorems/1261e1a5-9f3b-47d8-a9bd-c3ba6a43da6f
-- title:
--   Rg Eis: blk mul
-- statement:
--   The Rg Eis construction uses the blk mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L21-L28

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

theorem GlobalTheory.CompanionTheory.RgEis.blk_mul {S : Type} [CommRing S] (s : Set ι) [Fintype s] (x y : Matrix ι ι S)
    (hy : ∀ r, r ∉ s → ∀ c ∈ s, y r c = 0) :
    (x * y).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) =
      x.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) *
        y.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) := by sorry
