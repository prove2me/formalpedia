-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bdet_mul
-- name    : GlobalTheory.CompanionTheory.RgEis.bdet_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:57:41.472033+00:00
-- url     : https://prove2.me/theorems/6bf3d067-52a4-4c5e-806d-30efc6355fea
-- title:
--   Rg Eis: bdet mul
-- statement:
--   The Rg Eis construction uses the bdet mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L54-L59

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

theorem GlobalTheory.CompanionTheory.RgEis.bdet_mul (s : Set ι) {p q : GL ι R} (hp : p ∈ stab R s) (hq : q ∈ stab R s) :
    bdet s (p * q) = bdet s p * bdet s q := by sorry
