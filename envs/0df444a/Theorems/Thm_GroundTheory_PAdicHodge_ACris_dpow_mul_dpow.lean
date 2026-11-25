-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_dpow_mul_dpow
-- name    : GroundTheory.PAdicHodge.ACris.dpow_mul_dpow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:03:32.836825+00:00
-- url     : https://prove2.me/theorems/aaca2eaa-fc4e-4eed-a8c7-08e2ea17efb0
-- title:
--   ACris: dpow mul dpow
-- statement:
--   The ACris construction uses the dpow mul dpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FactorizationFactorialLe.lean#L135-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FactorizationFactorialLe.lean#L135-L148

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
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
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)

theorem GroundTheory.PAdicHodge.ACris.dpow_mul_dpow (m n : ℕ) (x : AInf K p) :
    dpow m x * dpow n x = ((m + n).choose m : 𝔸) * dpow (m + n) x := by sorry
