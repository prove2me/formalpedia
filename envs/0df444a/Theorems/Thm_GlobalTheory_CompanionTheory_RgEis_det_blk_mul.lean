-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_det_blk_mul
-- name    : GlobalTheory.CompanionTheory.RgEis.det_blk_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:17.952369+00:00
-- url     : https://prove2.me/theorems/499804b8-66bf-443b-8f5c-2addf8e2221c
-- title:
--   Rg Eis: det blk mul
-- statement:
--   The Rg Eis construction uses the det blk mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L31-L35

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

theorem GlobalTheory.CompanionTheory.RgEis.det_blk_mul (s : Set ι) (p : GL ι R) {q : GL ι R} (hq : q ∈ stab R s) :
    (((p * q : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det =
      ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det *
        ((q : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det := by sorry
