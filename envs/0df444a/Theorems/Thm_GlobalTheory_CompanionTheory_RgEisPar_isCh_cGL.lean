-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisPar_isCh_cGL
-- name    : GlobalTheory.CompanionTheory.RgEisPar.isCh_cGL
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:59:56.747597+00:00
-- url     : https://prove2.me/theorems/1cafcdbd-52e1-441c-a650-64fb3b730421
-- title:
--   Rg Eis Par: is Ch c GL
-- statement:
--   The Rg Eis Par construction uses the is Ch c GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ParabolicLawOfBlockDet.lean#L26-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ParabolicLawOfBlockDet.lean#L26-L43

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

theorem GlobalTheory.CompanionTheory.RgEisPar.isCh_cGL (hB : BdetLaw) (A : Ad E R) (hA : A.GoodL) (κ : Type) [Fintype κ] [DecidableEq κ] :
    IsCh (A.ratGL κ) ⊤ (A.cGL κ) := by sorry
