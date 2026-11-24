-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_bdet_split
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.bdet_split
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:59:00.222818+00:00
-- url     : https://prove2.me/theorems/eedd6970-af61-46b5-9d1a-bb076b298ad2
-- title:
--   Rg Eis Levi QUnit: bdet split
-- statement:
--   The Rg Eis Levi QUnit construction uses the bdet split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L622-L650
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L622-L650

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
  [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (A : Ad E R) (ε : ℤˣ) (hσ : ∀ x, A.σ (A.σ x) = x)
include hσ

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.bdet_split (p : A.uQ ε s) (hp : (p : A.U ε ι) ∈ A.uQ ε Set.univ) :
    bdet (Sum.inl '' (Set.univ : Set ι)) (p : A.U ε ι).1 =
      bdet (Sum.inl '' s) (p : A.U ε ι).1 *
        bdet (Sum.inl '' (Set.univ : Set ↥sᶜ)) (piQ A ε hσ p).1 := by sorry
