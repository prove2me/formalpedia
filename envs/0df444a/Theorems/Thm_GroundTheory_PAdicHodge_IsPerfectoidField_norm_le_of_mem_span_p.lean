-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_norm_le_of_mem_span_p
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.norm_le_of_mem_span_p
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:48.575184+00:00
-- url     : https://prove2.me/theorems/09ecaef0-78d9-44f2-af32-2e949d5c51c4
-- title:
--   Is Perfectoid Field: norm le of mem span p
-- statement:
--   The Is Perfectoid Field construction uses the norm le of mem span p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L101-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L101-L109

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
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
open WittVector
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
variable {p}
omit [Fact p.Prime] [IsPerfectoidField K p]

theorem GroundTheory.PAdicHodge.IsPerfectoidField.norm_le_of_mem_span_p {b : 𝒪} (hb : b ∈ Ideal.span {(p : 𝒪)}) :
    ‖(b : K)‖ ≤ ‖(p : K)‖ := by sorry
