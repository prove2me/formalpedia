-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IwaGen_exists_regular_point
-- name    : GlobalTheory.CompanionTheory.IwaGen.exists_regular_point
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:47:56.315665+00:00
-- url     : https://prove2.me/theorems/efe678f6-8788-4889-96ed-1dc8868bd5d5
-- title:
--   Iwa Gen: exists regular point
-- statement:
--   The Iwa Gen construction uses the exists regular point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsRegularElementAbelian.lean#L6-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsRegularElementAbelian.lean#L6-L44

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsRegularElementAbelian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwaGen

theorem GlobalTheory.CompanionTheory.IwaGen.exists_regular_point : ∀ {n : ℕ} (𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (U : Matrix (Fin n) (Fin n) ℂ), ∃ H ∈ 𝔞, ∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j →
      ∀ A ∈ 𝔞, (Uᴴ * A * U) i i = (Uᴴ * A * U) j j := by sorry
