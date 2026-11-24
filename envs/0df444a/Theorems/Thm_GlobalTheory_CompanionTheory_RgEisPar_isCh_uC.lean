-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisPar_isCh_uC
-- name    : GlobalTheory.CompanionTheory.RgEisPar.isCh_uC
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:59:26.119816+00:00
-- url     : https://prove2.me/theorems/409f602e-4fb4-4a4f-bba6-94941ba383b4
-- title:
--   Rg Eis Par: is Ch u C
-- statement:
--   The Rg Eis Par construction uses the is Ch u C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ParabolicLawOfBlockDet.lean#L79-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ParabolicLawOfBlockDet.lean#L79-L87

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicLawOfBlockDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisPar
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]

theorem GlobalTheory.CompanionTheory.RgEisPar.isCh_uC (hB : BdetLaw) (A : Ad E R) (hA : A.GoodL) (ε : ℤˣ) {κ : Type} [Fintype κ] [DecidableEq κ] :
    IsCh (A.uΓ ε κ) (A.uQ ε (Set.univ : Set κ)) (A.uC ε κ) := by sorry
