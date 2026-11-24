-- Prove2me | Theorems.Thm_GlobalTheory_isPreconnected_polydisc_first_coords_ne_zero
-- name    : GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:58:35.888008+00:00
-- url     : https://prove2.me/theorems/3116bf67-b598-419a-9b99-32f639acd6af
-- title:
--   Global Theory: is Preconnected polydisc first coords ne zero
-- statement:
--   The Global Theory construction uses the is Preconnected polydisc first coords ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsPreconnectedPolydiscFirstCoordsNeZero.lean#L28-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsPreconnectedPolydiscFirstCoordsNeZero.lean#L28-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPreconnectedPolydiscFirstCoordsNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set
open GlobalTheory

theorem GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero :
    ∀ (n a : ℕ) (ha : a ≤ n), _root_.IsPreconnected {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} := by sorry
