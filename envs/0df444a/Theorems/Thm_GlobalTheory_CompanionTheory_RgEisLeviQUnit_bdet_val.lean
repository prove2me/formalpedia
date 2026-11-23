-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_bdet_val
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.bdet_val
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:59.382513+00:00
-- url     : https://prove2.me/theorems/091f99ba-ce1d-4b11-a3f1-fb6078733e53
-- title:
--   Rg Eis Levi QUnit: bdet val
-- statement:
--   The Rg Eis Levi QUnit construction uses the bdet val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L483-L487
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L483-L487

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {R : Type} [CommRing R]
open Classical

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.bdet_val {α : Type} [Fintype α] [DecidableEq α] (S : Set α) (g : GL α R) (hg : g ∈ stab R S) :
    ((bdet S g : Rˣ) : R) = ((g : Matrix α α R).submatrix (Subtype.val : S → α) Subtype.val).det := by sorry
