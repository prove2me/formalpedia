-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_ker_le
-- name    : GroundTheory.PAdicHodge.WittTilt.gn_ker_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:48:48.203985+00:00
-- url     : https://prove2.me/theorems/24fdf5c5-0e4e-4df5-bf34-1ec8e26d178c
-- title:
--   Witt Tilt: gn ker le
-- statement:
--   The Witt Tilt construction uses the gn ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonNorm.lean#L193-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonNorm.lean#L193-L206

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

theorem GroundTheory.PAdicHodge.WittTilt.gn_ker_le (hp0 : ‖(p : K)‖ ≤ ρ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x : AInf K p}
    (hx : x ∈ RingHom.ker θ) : gn K p ρ (algebraMap (AInf K p) 𝔸 x) ≤ ρ := by sorry
