-- Prove2me | Theorems.Thm_GlobalTheory_isPreconnected_punctured_unit_disc
-- name    : GlobalTheory.isPreconnected_punctured_unit_disc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:58:41.000623+00:00
-- url     : https://prove2.me/theorems/99a2f88b-b286-4da6-9441-fc7eaa14b35b
-- title:
--   Global Theory: is Preconnected punctured unit disc
-- statement:
--   The Global Theory construction uses the is Preconnected punctured unit disc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsPreconnectedPolydiscFirstCoordsNeZero.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsPreconnectedPolydiscFirstCoordsNeZero.lean#L23-L26

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

theorem GlobalTheory.isPreconnected_punctured_unit_disc :
    IsPreconnected (Metric.ball (0:ℂ) 1 \ {0}) := by sorry
