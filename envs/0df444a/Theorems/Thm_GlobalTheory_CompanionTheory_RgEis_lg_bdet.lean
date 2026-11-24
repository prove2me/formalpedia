-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_lg_bdet
-- name    : GlobalTheory.CompanionTheory.RgEis.lg_bdet
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:28.565323+00:00
-- url     : https://prove2.me/theorems/e230eb7b-13bf-4422-84d8-3fa536347c8f
-- title:
--   Rg Eis: lg bdet
-- statement:
--   The Rg Eis construction uses the lg bdet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L212-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L212-L223

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
variable [TopologicalSpace R] [IsTopologicalRing R]
open Classical

theorem GlobalTheory.CompanionTheory.RgEis.lg_bdet (A : Ad E R) (hA : A.GoodL) (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s)
    (hk : p ∈ A.kGL ι) : A.lg (bdet s p) = 0 := by sorry
