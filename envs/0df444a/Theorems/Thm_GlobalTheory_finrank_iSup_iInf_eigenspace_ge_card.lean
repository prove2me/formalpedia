-- Prove2me | Theorems.Thm_GlobalTheory_finrank_iSup_iInf_eigenspace_ge_card
-- name    : GlobalTheory.finrank_iSup_iInf_eigenspace_ge_card
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:49:21.795884+00:00
-- url     : https://prove2.me/theorems/239605f8-f368-4ee0-8714-b3295938be96
-- title:
--   Global Theory: finrank i Sup i Inf eigenspace ge card
-- statement:
--   The Global Theory construction uses the finrank i Sup i Inf eigenspace ge card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardLeFinrankSupEigenspaces.lean#L5-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardLeFinrankSupEigenspaces.lean#L5-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardLeFinrankSupEigenspaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.finrank_iSup_iInf_eigenspace_ge_card : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (O : Type) (T : O → Module.End ℂ W),
    (∀ a b, Commute (T a) (T b)) → ∀ (I : Type) [Fintype I] (ψ : I → O → ℂ), Function.Injective ψ →
    (∀ i, 1 ≤ Module.finrank ℂ (⨅ a, Module.End.eigenspace (T a) (ψ i a) : Submodule ℂ W)) →
    Fintype.card I ≤ Module.finrank ℂ (⨆ i, ⨅ a, Module.End.eigenspace (T a) (ψ i a) : Submodule ℂ W) := by sorry
