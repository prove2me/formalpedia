-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bdet_val
-- name    : GlobalTheory.CompanionTheory.RgEis.bdet_val
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:43.689511+00:00
-- url     : https://prove2.me/theorems/8c337f60-f040-4b00-9b2f-3c733f290d5e
-- title:
--   Rg Eis: bdet val
-- statement:
--   The Rg Eis construction uses the bdet val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L50-L52

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

theorem GlobalTheory.CompanionTheory.RgEis.bdet_val (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) :
    ((bdet s p : Rˣ) : R) = ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det := by sorry
