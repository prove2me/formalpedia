-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_acrisZero_le_one
-- name    : GroundTheory.PAdicHodge.WittTilt.gn_acrisZero_le_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:47:26.430072+00:00
-- url     : https://prove2.me/theorems/eccbfbc2-4fc6-4f54-a356-d9d5f43dc36a
-- title:
--   Witt Tilt: gn acris Zero le one
-- statement:
--   The Witt Tilt construction uses the gn acris Zero le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonNorm.lean#L222-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonNorm.lean#L222-L234

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

theorem GroundTheory.PAdicHodge.WittTilt.gn_acrisZero_le_one (hp0 : ‖(p : K)‖ ≤ ρ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {z : 𝔸}
    (hz : z ∈ ACris.ACrisZero K p) : gn K p ρ z ≤ 1 := by sorry
