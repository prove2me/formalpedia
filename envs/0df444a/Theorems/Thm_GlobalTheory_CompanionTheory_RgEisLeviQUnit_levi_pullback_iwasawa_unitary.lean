-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_levi_pullback_iwasawa_unitary
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.levi_pullback_iwasawa_unitary
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:59:38.245809+00:00
-- url     : https://prove2.me/theorems/e4cf95f9-29d7-4a83-9be7-558a5b24d850
-- title:
--   Rg Eis Levi QUnit: levi pullback iwasawa unitary
-- statement:
--   The Rg Eis Levi QUnit construction uses the levi pullback iwasawa unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L756-L806
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L756-L806

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

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.levi_pullback_iwasawa_unitary (hB : BdetLaw) (hE : ExtLaw) (hT : GrpTop) (hA : A.Good)
    (hI : Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι)) :
    ∃ (π : A.uQ ε s →* A.U ε ↥sᶜ) (j : A.U ε ↥sᶜ →* A.uQ ε s) (c : A.U ε ι → ℂ),
      IsLevi (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε s) (A.uΓ ε _) (A.uK ε _) π j c ∧
      IsPull (A.uQ ε s) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uQ ε Set.univ) π c (A.uC ε ι) (A.uC ε _) ∧
      Iwa (A.uQ ε (Set.univ : Set ↥sᶜ)) (A.uK ε _) ∧
      PullHt (A.uK ε ι) (A.uQ ε s) π (fun g => A.uH ε Set.univ g - A.uH ε s g) (A.uH ε Set.univ) := by sorry
