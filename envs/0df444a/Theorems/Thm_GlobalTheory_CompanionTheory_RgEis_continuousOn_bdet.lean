-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_continuousOn_bdet
-- name    : GlobalTheory.CompanionTheory.RgEis.continuousOn_bdet
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:57:46.54418+00:00
-- url     : https://prove2.me/theorems/1b781489-0394-41fc-af52-681b0a13071c
-- title:
--   Rg Eis: continuous On bdet
-- statement:
--   The Rg Eis construction uses the continuous On bdet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L94-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L94-L109

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
variable [TopologicalSpace R] [IsTopologicalRing R]

theorem GlobalTheory.CompanionTheory.RgEis.continuousOn_bdet (s : Set ι) :
    ContinuousOn (bdet s) (stab R s : Set (GL ι R)) := by sorry
