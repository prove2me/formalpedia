-- Prove2me | Theorems.Thm_GroundTheory_Global_geom_sum_le_exp
-- name    : GroundTheory.Global.geom_sum_le_exp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:41:35.343945+00:00
-- url     : https://prove2.me/theorems/7d8e4c58-6c4f-418f-9b4e-ddd0ede2e0a0
-- title:
--   Global: geom sum le exp
-- statement:
--   The Global construction uses the geom sum le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L73-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L73-L84

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

theorem GroundTheory.Global.geom_sum_le_exp {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (M : ℕ) :
    ∑ k ∈ Finset.range M, x ^ k ≤ Real.exp (x + 2 * x ^ 2) := by sorry
