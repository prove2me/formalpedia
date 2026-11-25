-- Prove2me | Theorems.Thm_GlobalTheory_SpectralLemmaSecond_main
-- name    : GlobalTheory.SpectralLemmaSecond.main
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:17.35231+00:00
-- url     : https://prove2.me/theorems/832af9a6-4c1e-47d5-b5a6-68bf648e8545
-- title:
--   Spectral Lemma Second: main
-- statement:
--   The Spectral Lemma Second construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsFurtherExtra.lean#L7-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsFurtherExtra.lean#L7-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsFurtherExtra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SpectralLemmaSecond
open Matrix

theorem GlobalTheory.SpectralLemmaSecond.main : (let d1 : {m k : Type} → [Fintype m] → [Fintype k] → Matrix m k ℂ → ℝ := @(fun {m k : Type} [Fintype m] [Fintype k] (M : Matrix m k ℂ) ↦ ∑ i : m, ∑ j : k, ‖M i j‖); ∀ {m k p : Type} [inst : Fintype m] [inst_1 : Fintype k] [inst_2 : Fintype p] (M : Matrix m k ℂ) (N : Matrix k p ℂ), d1 (M * N) ≤ d1 M * d1 N) := by sorry
