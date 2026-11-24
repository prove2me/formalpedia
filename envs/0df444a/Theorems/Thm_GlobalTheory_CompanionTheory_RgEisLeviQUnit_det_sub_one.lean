-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_det_sub_one
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.det_sub_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:59:48.090228+00:00
-- url     : https://prove2.me/theorems/2fc3fa8a-dcc6-45e3-bc65-207444270803
-- title:
--   Rg Eis Levi QUnit: det sub one
-- statement:
--   The Rg Eis Levi QUnit construction uses the det sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L489-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L489-L495

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

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.det_sub_one {α : Type} [Fintype α] [DecidableEq α] {S : Set α} {_ : Fintype S} {_ : DecidableEq S}
    (g : Matrix α α R) (h : ∀ a b : S, g a.1 b.1 = if a = b then 1 else 0) :
    (g.submatrix (Subtype.val : S → α) Subtype.val).det = 1 := by sorry
