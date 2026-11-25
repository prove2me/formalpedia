-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_mem_Ioc
-- name    : GroundTheory.PAdicHodge.exists_norm_mem_Ioc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:52:46.093949+00:00
-- url     : https://prove2.me/theorems/0bd853ae-158f-4efb-ab0f-432f5f5b3718
-- title:
--   PAdic Hodge: exists norm mem Ioc
-- statement:
--   The PAdic Hodge construction uses the exists norm mem Ioc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltAlgebra.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltAlgebra.lean#L83-L85

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

theorem GroundTheory.PAdicHodge.exists_norm_mem_Ioc (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ x : K, a < ‖x‖ ∧ ‖x‖ ≤ b := by sorry
