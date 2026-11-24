-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bdet_univ
-- name    : GlobalTheory.CompanionTheory.RgEis.bdet_univ
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:57:36.801361+00:00
-- url     : https://prove2.me/theorems/050a267c-50a5-4c40-90bd-f5b334f9ea50
-- title:
--   Rg Eis: bdet univ
-- statement:
--   The Rg Eis construction uses the bdet univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L68-L75

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

theorem GlobalTheory.CompanionTheory.RgEis.bdet_univ (g : GL ι R) : bdet (Set.univ : Set ι) g = Matrix.GeneralLinearGroup.det g := by sorry
