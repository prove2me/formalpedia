-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_block_unit
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.block_unit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:58:46.087949+00:00
-- url     : https://prove2.me/theorems/4d93ffe6-1ce1-4dd4-9e92-600f0ce417d2
-- title:
--   Rg Eis Levi QUnit: block unit
-- statement:
--   The Rg Eis Levi QUnit construction uses the block unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L471-L480
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L471-L480

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

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.block_unit {α : Type} [Fintype α] [DecidableEq α] {S : Set α} [Fintype S] [DecidableEq S] (g : GL α R)
    (hg : g ∈ stab R S) : IsUnit ((g : Matrix α α R).submatrix (Subtype.val : S → α) Subtype.val).det := by sorry
