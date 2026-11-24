-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_comb_le
-- name    : GlobalTheory.CompanionTheory.AnalyticWord.comb_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:18:01.133263+00:00
-- url     : https://prove2.me/theorems/82a90ea5-1d86-40e6-833f-53836920b102
-- title:
--   Analytic Word: comb le
-- statement:
--   The Analytic Word construction uses the comb le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L62-L67

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

theorem GlobalTheory.CompanionTheory.AnalyticWord.comb_le {l : List ι} {k : ℕ} (hl : l.length = k) (a : Fin m → ℂ) :
    ‖j (word Z l (∑ f, a f • y f))‖ ≤ (∑ f, ‖a f‖) * bnd j Z y k := by sorry
