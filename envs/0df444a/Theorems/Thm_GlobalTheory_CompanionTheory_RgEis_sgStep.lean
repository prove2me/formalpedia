-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_sgStep
-- name    : GlobalTheory.CompanionTheory.RgEis.sgStep
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:57:04.155387+00:00
-- url     : https://prove2.me/theorems/7c1d7521-ace1-4a08-aff6-17ede3ef4180
-- title:
--   Rg Eis: sg Step
-- statement:
--   The Rg Eis construction uses the sg Step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SiegelInductionFromGallery.lean#L128-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SiegelInductionFromGallery.lean#L128-L163

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SiegelInductionFromGallery
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]
open Classical

theorem GlobalTheory.CompanionTheory.RgEis.sgStep : Gallery → Transfer → Twist → GrpTop → ParLaw → LeviS → LeviQ → ConvGrOf → ConvU → SgStep := by sorry
