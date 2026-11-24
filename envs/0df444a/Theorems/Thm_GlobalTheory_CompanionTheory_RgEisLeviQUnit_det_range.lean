-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_det_range
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.det_range
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:58:52.584076+00:00
-- url     : https://prove2.me/theorems/7053aa9f-832f-4b59-a662-b3aca7f4b8f0
-- title:
--   Rg Eis Levi QUnit: det range
-- statement:
--   The Rg Eis Levi QUnit construction uses the det range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L497-L502
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L497-L502

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

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.det_range {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (f : β → α)
    (hf : Function.Injective f) (T : Set α) (hT : T = Set.range f) {_ : Fintype T} {_ : DecidableEq T} (g : Matrix α α R) :
    (g.submatrix (Subtype.val : T → α) Subtype.val).det = (g.submatrix f f).det := by sorry
