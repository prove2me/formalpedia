-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_mem_Ioc_of_dense
-- name    : GroundTheory.PAdicHodge.exists_norm_mem_Ioc_of_dense
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:12.57491+00:00
-- url     : https://prove2.me/theorems/64dedc58-ba1c-40f4-a41f-1282e2ea2c53
-- title:
--   PAdic Hodge: exists norm mem Ioc of dense
-- statement:
--   The PAdic Hodge construction uses the exists norm mem Ioc of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltAlgebra.lean#L53-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltAlgebra.lean#L53-L81

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
omit [IsUltrametricDist K]

theorem GroundTheory.PAdicHodge.exists_norm_mem_Ioc_of_dense (hnd : ∀ r : ℝ, r < 1 → ∃ x : K, r < ‖x‖ ∧ ‖x‖ < 1)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) : ∃ x : K, a < ‖x‖ ∧ ‖x‖ ≤ b := by sorry
