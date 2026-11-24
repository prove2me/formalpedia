-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_det_blk_mul_inv
-- name    : GlobalTheory.CompanionTheory.RgEis.det_blk_mul_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:49.609996+00:00
-- url     : https://prove2.me/theorems/97c5e29f-adb9-4ebf-8279-8a2fa187bd60
-- title:
--   Rg Eis: det blk mul inv
-- statement:
--   The Rg Eis construction uses the det blk mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L38-L42

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

theorem GlobalTheory.CompanionTheory.RgEis.det_blk_mul_inv (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) :
    ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det *
      (((p⁻¹ : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det = 1 := by sorry
