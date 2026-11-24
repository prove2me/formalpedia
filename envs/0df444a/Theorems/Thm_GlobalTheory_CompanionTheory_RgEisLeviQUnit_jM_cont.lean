-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_jM_cont
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.jM_cont
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:59:11.914675+00:00
-- url     : https://prove2.me/theorems/f87fbf12-9ba9-4de1-9ff2-85e10b8ca83f
-- title:
--   Rg Eis Levi QUnit: j M cont
-- statement:
--   The Rg Eis Levi QUnit construction uses the j M cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L662-L664
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L662-L664

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
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (A : Ad E R) (ε : ℤˣ)

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.jM_cont : Continuous (jM (emb s) : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R → Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by sorry
