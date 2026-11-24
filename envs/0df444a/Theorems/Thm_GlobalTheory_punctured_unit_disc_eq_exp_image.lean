-- Prove2me | Theorems.Thm_GlobalTheory_punctured_unit_disc_eq_exp_image
-- name    : GlobalTheory.punctured_unit_disc_eq_exp_image
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:15:27.121132+00:00
-- url     : https://prove2.me/theorems/95511e2c-c2b5-42b1-b8de-d09b95b8e841
-- title:
--   Global Theory: punctured unit disc eq exp image
-- statement:
--   The Global Theory construction uses the punctured unit disc eq exp image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsPreconnectedPolydiscFirstCoordsNeZero.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsPreconnectedPolydiscFirstCoordsNeZero.lean#L7-L21

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

theorem GlobalTheory.punctured_unit_disc_eq_exp_image :
    Metric.ball (0:ℂ) 1 \ {0} = Complex.exp '' {z : ℂ | z.re < 0} := by sorry
