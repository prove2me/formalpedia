-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_comm_S
-- name    : GlobalTheory.CompanionTheory.AnalyticWord.comm_S
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:18:00.022735+00:00
-- url     : https://prove2.me/theorems/6d6f4bc7-ac7a-4535-a5dc-f4cbbe9712d9
-- title:
--   Analytic Word: comm S
-- statement:
--   The Analytic Word construction uses the comm S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L81-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L81-L93

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

theorem GlobalTheory.CompanionTheory.AnalyticWord.comm_S (Z : ι → Module.End ℂ V) [Fintype ι] (K : Finset ι) (c : ι → ι → ι → ℂ)
    (hcomm : ∀ κ i, Z κ * Z i - Z i * Z κ = ∑ l, c κ i l • Z l) (i : ι) :
    (∑ κ ∈ K, Z κ * Z κ) * Z i - Z i * (∑ κ ∈ K, Z κ * Z κ) =
      ∑ κ ∈ K, ∑ n, c κ i n • (Z κ * Z n + Z n * Z κ) := by sorry
