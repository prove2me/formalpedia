-- Prove2me | Theorems.Thm_GlobalTheory_T_isPreconnected_ball_inter_coords_ne_zero
-- name    : GlobalTheory.T.isPreconnected_ball_inter_coords_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:36:18.148335+00:00
-- url     : https://prove2.me/theorems/f772bed8-116c-4ca5-b0b7-e03dc32ec6ab
-- title:
--   T: is Preconnected ball inter coords ne zero
-- statement:
--   The T construction uses the is Preconnected ball inter coords ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsPreconnectedPolydiscFirstCoordsNeZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsPreconnectedPolydiscFirstCoordsNeZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPreconnectedPolydiscFirstCoordsNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPreconnectedPolydiscFirstCoordsNeZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isPreconnected_ball_inter_coords_ne_zero : ∀ (n a : ℕ) (ha : a ≤ n), _root_.IsPreconnected {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} := by sorry
