-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_jM_off_left
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.jM_off_left
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:59:46.803023+00:00
-- url     : https://prove2.me/theorems/38f15475-35d6-4139-84cb-a39e46b8a099
-- title:
--   Rg Eis Levi QUnit: j M off left
-- statement:
--   The Rg Eis Levi QUnit construction uses the j M off left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L126-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L126-L133

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

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.jM_off_left (e : κ → α) (m : Matrix κ κ R) (a b : α) (h : a ∉ Set.range e) :
    jM e m a b = (1 : Matrix α α R) a b := by sorry
