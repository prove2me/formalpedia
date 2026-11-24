-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdProj_mem_of_entrywise
-- name    : GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:16:13.18831+00:00
-- url     : https://prove2.me/theorems/1cc4dff2-281a-457e-af69-c1b518e9fba5
-- title:
--   Ad Proj: mem of entrywise
-- statement:
--   The Ad Proj construction uses the mem of entrywise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraFunctionCalculus.lean#L68-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraFunctionCalculus.lean#L68-L83

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraFunctionCalculus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdProj

theorem GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ) :
    Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤 → (∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) →
      ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤 := by sorry
