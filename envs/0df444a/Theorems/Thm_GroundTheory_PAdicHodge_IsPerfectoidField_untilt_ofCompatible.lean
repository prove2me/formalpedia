-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_ofCompatible
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.untilt_ofCompatible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:41.651171+00:00
-- url     : https://prove2.me/theorems/89cb106f-47a1-457c-8bf1-3bf3c2805d85
-- title:
--   Is Perfectoid Field: untilt of Compatible
-- statement:
--   The Is Perfectoid Field construction uses the untilt of Compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L187-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L187-L194

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.untilt_ofCompatible (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n) :
    PreTilt.untilt (ofCompatible p y hy) = y 0 := by sorry
