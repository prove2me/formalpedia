-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_tot_nonneg
-- name    : GlobalTheory.CompanionTheory.AnalyticWord.tot_nonneg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:17:31.974173+00:00
-- url     : https://prove2.me/theorems/a367e751-012f-47e8-901a-5fe20f4d5d81
-- title:
--   Analytic Word: tot nonneg
-- statement:
--   The Analytic Word construction uses the tot nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L198-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L198-L200

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnalyticWord
variable {V H : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type}
variable [Fintype ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V) {m : ℕ} (y : Fin m → V)
  (S Ω : Module.End ℂ V) (K : Finset ι) (c : ι → ι → ι → ℂ) (d o : Fin m → Fin m → ℂ)

theorem GlobalTheory.CompanionTheory.AnalyticWord.tot_nonneg (a : Fin m → Fin m → ℂ) : 0 ≤ tot a := by sorry
