-- Prove2me | Theorems.Thm_GlobalTheory_NormPowSubOne_main
-- name    : GlobalTheory.NormPowSubOne.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:01.816469+00:00
-- url     : https://prove2.me/theorems/bf3d72b6-9567-44d0-a207-1543e037682d
-- title:
--   Norm Pow Sub One: main
-- statement:
--   The Norm Pow Sub One construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormPowSubOneLe.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormPowSubOneLe.lean#L18-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormPowSubOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.NormPowSubOne

theorem GlobalTheory.NormPowSubOne.main : ∀ {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K] {ζ : K},
    ‖ζ‖ = (1 : ℝ) → ∀ (a : ℕ), ‖ζ ^ a - (1 : K)‖ ≤ ‖ζ - (1 : K)‖ := by sorry
