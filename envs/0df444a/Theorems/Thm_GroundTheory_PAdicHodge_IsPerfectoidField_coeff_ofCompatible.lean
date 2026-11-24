-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_coeff_ofCompatible
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.coeff_ofCompatible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:45.115253+00:00
-- url     : https://prove2.me/theorems/1da6d301-ae88-4fa0-8cf5-0fd06f60049e
-- title:
--   Is Perfectoid Field: coeff of Compatible
-- statement:
--   The Is Perfectoid Field construction uses the coeff of Compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L183-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L183-L185

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.coeff_ofCompatible (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n) (n : ℕ) :
    PreTilt.coeff n (ofCompatible p y hy) = Ideal.Quotient.mk _ (y n) := by sorry
