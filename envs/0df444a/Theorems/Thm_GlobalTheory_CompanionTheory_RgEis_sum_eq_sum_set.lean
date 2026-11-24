-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_sum_eq_sum_set
-- name    : GlobalTheory.CompanionTheory.RgEis.sum_eq_sum_set
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:57:03.186582+00:00
-- url     : https://prove2.me/theorems/f6956f5e-69fd-4560-b3dc-c4384d0ec800
-- title:
--   Rg Eis: sum eq sum set
-- statement:
--   The Rg Eis construction uses the sum eq sum set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L15-L19

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

theorem GlobalTheory.CompanionTheory.RgEis.sum_eq_sum_set {S : Type} [AddCommMonoid S] (s : Set ι) [Fintype s] (f : ι → S)
    (h : ∀ m, m ∉ s → f m = 0) : ∑ m, f m = ∑ m : s, f m := by sorry
