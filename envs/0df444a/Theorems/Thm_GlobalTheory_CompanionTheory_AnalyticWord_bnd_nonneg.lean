-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_bnd_nonneg
-- name    : GlobalTheory.CompanionTheory.AnalyticWord.bnd_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:10.695374+00:00
-- url     : https://prove2.me/theorems/49221ac9-ee1d-429a-8774-20a813bac37f
-- title:
--   Analytic Word: bnd nonneg
-- statement:
--   The Analytic Word construction uses the bnd nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L36-L38

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
variable [Finite ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V) {m : ℕ} (y : Fin m → V)

theorem GlobalTheory.CompanionTheory.AnalyticWord.bnd_nonneg (k : ℕ) : 0 ≤ bnd j Z y k := by sorry
