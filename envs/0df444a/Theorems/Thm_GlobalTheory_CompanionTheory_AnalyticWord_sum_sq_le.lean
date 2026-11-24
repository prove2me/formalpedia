-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_sum_sq_le
-- name    : GlobalTheory.CompanionTheory.AnalyticWord.sum_sq_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:18:08.315874+00:00
-- url     : https://prove2.me/theorems/4d18b83e-fe10-4d34-8a90-3563be68a1af
-- title:
--   Analytic Word: sum sq le
-- statement:
--   The Analytic Word construction uses the sum sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L95-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L95-L115

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

theorem GlobalTheory.CompanionTheory.AnalyticWord.sum_sq_le [Fintype ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V)
    (hskew : ∀ i v w, inner ℂ (j (Z i v)) (j w) = - inner ℂ (j v) (j (Z i w)))
    (S Ω : Module.End ℂ V) (hT : ∑ i, Z i * Z i = Ω + S + S) (v : V) (i : ι) :
    ‖j (Z i v)‖ ^ 2 ≤ ‖j v‖ * (‖j (Ω v)‖ + 2 * ‖j (S v)‖) := by sorry
