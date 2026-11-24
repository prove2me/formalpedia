-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bdet_rat
-- name    : GlobalTheory.CompanionTheory.RgEis.bdet_rat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:57:44.755822+00:00
-- url     : https://prove2.me/theorems/8cff90d7-d809-4bea-97f0-71630e50532a
-- title:
--   Rg Eis: bdet rat
-- statement:
--   The Rg Eis construction uses the bdet rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L119-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L119-L136

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
variable {E : Type} [Field E]
open Classical

theorem GlobalTheory.CompanionTheory.RgEis.bdet_rat (A : Ad E R) (hi : Function.Injective A.i) (s : Set ι) {p : GL ι R}
    (hp : p ∈ stab R s) (hr : p ∈ A.ratGL ι) : ∃ x, bdet s p = Units.map A.i.toMonoidHom x := by sorry
