-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_pull_mem
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.pull_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:52.371373+00:00
-- url     : https://prove2.me/theorems/59a069d6-ec90-49a7-9698-301e7c94c476
-- title:
--   Rg Eis Levi QUnit: pull mem
-- statement:
--   The Rg Eis Levi QUnit construction uses the pull mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L595-L619
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L595-L619

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

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.pull_mem (g : A.U ε ι) : g ∈ A.uQ ε s ⊓ A.uQ ε Set.univ ↔
    ∃ hg : g ∈ A.uQ ε s, piQ A ε hσ ⟨g, hg⟩ ∈ A.uQ ε (Set.univ : Set ↥sᶜ) := by sorry
