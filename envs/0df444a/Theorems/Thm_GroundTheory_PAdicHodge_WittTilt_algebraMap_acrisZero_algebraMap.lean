-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_algebraMap_acrisZero_algebraMap
-- name    : GroundTheory.PAdicHodge.WittTilt.algebraMap_acrisZero_algebraMap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:30.668116+00:00
-- url     : https://prove2.me/theorems/61547002-e87c-5c3e-a6e5-e132f1fde1af
-- title:
--   Witt Tilt: algebra Map acris Zero algebra Map
-- statement:
--   The Witt Tilt construction uses the algebra Map acris Zero algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonDom.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonDom.lean#L37-L40

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonApprox
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonDom
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
open _root_.WittVector Laurent ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝔸" => Localization.Away (p : AInf K p)
variable {ρ : ℝ}

theorem GroundTheory.PAdicHodge.WittTilt.algebraMap_acrisZero_algebraMap (w : AInf K p) :
    algebraMap (ACrisZero K p) (ACris K p) (algebraMap (AInf K p) (ACrisZero K p) w) =
      algebraMap (AInf K p) (ACris K p) w := by sorry
