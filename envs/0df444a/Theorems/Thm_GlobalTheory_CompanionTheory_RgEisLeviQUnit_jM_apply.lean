-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_jM_apply
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.jM_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:59:25.593093+00:00
-- url     : https://prove2.me/theorems/1b82af82-666b-400f-97f4-c2105fd00d0b
-- title:
--   Rg Eis Levi QUnit: j M apply
-- statement:
--   The Rg Eis Levi QUnit construction uses the j M apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L147-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L147-L150

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

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.jM_apply {e : κ → α} (he : Function.Injective e) (m : Matrix κ κ R) (x y : κ) :
    jM e m (e x) (e y) = m x y := by sorry
