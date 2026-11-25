-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_exists_toB_mul
-- name    : GroundTheory.PAdicHodge.WittTilt.exists_toB_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:45:41.884361+00:00
-- url     : https://prove2.me/theorems/d7045b00-817e-58c1-99d3-b0cea56d5da4
-- title:
--   Witt Tilt: exists to B mul
-- statement:
--   The Witt Tilt construction uses the exists to B mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonNorm.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonNorm.lean#L41-L50

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

theorem GroundTheory.PAdicHodge.WittTilt.exists_toB_mul (z : 𝔸) : ∃ (M : ℕ) (x : AInf K p),
    toB K p z * algebraMap _ (teichLift K p).B (teichLift K p).π ^ M =
      algebraMap _ (teichLift K p).B (incl K p x) := by sorry
