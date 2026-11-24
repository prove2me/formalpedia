-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_lifts_of_separable_reduction
-- name    : GlobalTheory.T.exists_lifts_of_separable_reduction
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:16:50.717796+00:00
-- url     : https://prove2.me/theorems/26bd0e99-6308-4f48-b692-3a9f1e527a7d
-- title:
--   T: exists lifts of separable reduction
-- statement:
--   The T construction uses the exists lifts of separable reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftsOfSeparableStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftsOfSeparableStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftsOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftsOfSeparableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_lifts_of_separable_reduction : ∀ (D : ℕ) (P : Polynomial (MvPowerSeries (Fin D) ℂ)), P.Monic → (P.map (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ))).Separable → ∃ θ : Fin P.natDegree → MvPowerSeries (Fin D) ℂ, Function.Injective θ ∧ ∀ j, P.IsRoot (θ j) := by sorry
