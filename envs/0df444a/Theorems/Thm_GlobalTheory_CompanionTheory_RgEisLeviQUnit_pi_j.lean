-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_pi_j
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.pi_j
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:59:46.866743+00:00
-- url     : https://prove2.me/theorems/667dd56b-3a1f-4f23-8c94-8b5f501857e1
-- title:
--   Rg Eis Levi QUnit: pi j
-- statement:
--   The Rg Eis Levi QUnit construction uses the pi j property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L462-L463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L462-L463

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
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι}
variable [Fintype ↥sᶜ] [DecidableEq ↥sᶜ]
variable (A : Ad E R) (ε : ℤˣ)

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.pi_j (hσ : ∀ x, A.σ (A.σ x) = x) (m : A.U ε ↥sᶜ) : piQ A ε hσ (jQ (s := s) A ε m) = m := by sorry
