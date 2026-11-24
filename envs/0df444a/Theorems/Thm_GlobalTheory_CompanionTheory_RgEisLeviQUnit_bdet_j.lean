-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_bdet_j
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.bdet_j
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:59:34.502146+00:00
-- url     : https://prove2.me/theorems/60474f9a-f618-40c6-9573-c0b78f2aa192
-- title:
--   Rg Eis Levi QUnit: bdet j
-- statement:
--   The Rg Eis Levi QUnit construction uses the bdet j property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L743-L754
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L743-L754

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
variable [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] (A : Ad E R) (ε : ℤˣ)
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} {_fF : Fintype ↥sᶜ} {_fD : DecidableEq ↥sᶜ}

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.bdet_j (m : A.U ε ↥sᶜ) : bdet (Sum.inl '' s) (jQ (s := s) A ε m : A.U ε ι).1 = 1 := by sorry
