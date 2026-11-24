-- Prove2me | Theorems.Thm_GroundTheory_Global_exp_sub_sq_le_one_add
-- name    : GroundTheory.Global.exp_sub_sq_le_one_add
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:18.800817+00:00
-- url     : https://prove2.me/theorems/8e083bd1-6764-41c0-a1f8-3f35dc71fb98
-- title:
--   Global: exp sub sq le one add
-- statement:
--   The Global construction uses the exp sub sq le one add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L86-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L86-L92

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.exp_sub_sq_le_one_add {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (x - x ^ 2) ≤ 1 + x := by sorry
