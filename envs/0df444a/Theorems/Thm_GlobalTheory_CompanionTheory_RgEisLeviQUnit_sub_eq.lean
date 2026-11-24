-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_sub_eq
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.sub_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:59:31.466984+00:00
-- url     : https://prove2.me/theorems/5db37617-0afb-43d2-b14a-03ea405fccd0
-- title:
--   Rg Eis Levi QUnit: sub eq
-- statement:
--   The Rg Eis Levi QUnit construction uses the sub eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L110-L113

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
variable {α κ β : Type} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.sub_eq (e : κ → α) (g : Matrix α α R) : g.submatrix e e = (Pm R e)ᵀ * g * Pm R e := by sorry
