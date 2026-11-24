-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_lg_eq_zero
-- name    : GlobalTheory.CompanionTheory.RgEis.lg_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:38.745623+00:00
-- url     : https://prove2.me/theorems/61ce1412-0be0-4c40-b9c6-1e9e08a9e440
-- title:
--   Rg Eis: lg eq zero
-- statement:
--   The Rg Eis construction uses the lg eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L161-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockDeterminantLaw.lean#L161-L208

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

theorem GlobalTheory.CompanionTheory.RgEis.lg_eq_zero (A : Ad E R) (hA : A.GoodL) (u : Rˣ) (h1 : (u : R) ∈ A.O)
    (h2 : ((u⁻¹ : Rˣ) : R) ∈ A.O) (hw : ∀ w, ‖A.φ w (u : R)‖ = 1) : A.lg u = 0 := by sorry
