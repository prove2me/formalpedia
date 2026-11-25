-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_norm_zcoeff_incl_le_one
-- name    : GroundTheory.PAdicHodge.WittTilt.norm_zcoeff_incl_le_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:47:29.10923+00:00
-- url     : https://prove2.me/theorems/db39594e-bbb7-4ae3-b3b6-46e86e81bc2c
-- title:
--   Witt Tilt: norm zcoeff incl le one
-- statement:
--   The Witt Tilt construction uses the norm zcoeff incl le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonNorm.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonNorm.lean#L24-L29

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

theorem GroundTheory.PAdicHodge.WittTilt.norm_zcoeff_incl_le_one (x : AInf K p) (n : ℤ) :
    ‖(teichLift K p).zcoeff (incl K p x) n‖ ≤ 1 := by sorry
