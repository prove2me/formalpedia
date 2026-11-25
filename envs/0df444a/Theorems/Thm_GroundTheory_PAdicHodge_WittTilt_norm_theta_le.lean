-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_norm_theta_le
-- name    : GroundTheory.PAdicHodge.WittTilt.norm_theta_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:32.087434+00:00
-- url     : https://prove2.me/theorems/385ff4c5-5d8e-407a-b4ee-5c65746d68f3
-- title:
--   Witt Tilt: norm theta le
-- statement:
--   The Witt Tilt construction uses the norm theta le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonNorm.lean#L242-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonNorm.lean#L242-L273

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
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
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector Laurent
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p
variable {ρ : ℝ}
variable [CharZero K]

theorem GroundTheory.PAdicHodge.WittTilt.norm_theta_le (x : AInf K p) :
    ‖((θ x : 𝒪) : K)‖ ≤ gn K p ‖(p : K)‖ (algebraMap (AInf K p) 𝔸 x) := by sorry
