-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_dpow_mul
-- name    : GroundTheory.PAdicHodge.ACris.dpow_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:03:12.936189+00:00
-- url     : https://prove2.me/theorems/0d6c1831-c220-4ce9-880b-f890cb38cfac
-- title:
--   ACris: dpow mul
-- statement:
--   The ACris construction uses the dpow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FactorizationFactorialLe.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FactorizationFactorialLe.lean#L131-L133

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

theorem GroundTheory.PAdicHodge.ACris.dpow_mul (n : ℕ) (x y : AInf K p) :
    dpow n (x * y) = dpow n x * algebraMap (AInf K p) 𝔸 y ^ n := by sorry
