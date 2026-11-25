-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isPrincipal_ker_fontaineTheta
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.isPrincipal_ker_fontaineTheta
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:58.757915+00:00
-- url     : https://prove2.me/theorems/2dfa09a3-3dc5-4798-bd22-1b552fe9ac07
-- title:
--   Is Perfectoid Field: is Principal ker fontaine Theta
-- statement:
--   The Is Perfectoid Field construction uses the is Principal ker fontaine Theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L447-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L447-L449

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
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
variable (K p)

theorem GroundTheory.PAdicHodge.IsPerfectoidField.isPrincipal_ker_fontaineTheta : (RingHom.ker θ).IsPrincipal := by sorry
