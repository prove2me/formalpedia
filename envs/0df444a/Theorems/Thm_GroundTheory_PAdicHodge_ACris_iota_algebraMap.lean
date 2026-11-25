-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_iota_algebraMap
-- name    : GroundTheory.PAdicHodge.ACris.iota_algebraMap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:29.779861+00:00
-- url     : https://prove2.me/theorems/295f4f22-157a-43a1-9cc5-6f4812bcdb23
-- title:
--   ACris: iota algebra Map
-- statement:
--   The ACris construction uses the iota algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdR.lean#L401-L404
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdR.lean#L401-L404

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_BdRLattice
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_PrecompleteOfSurjective
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)

theorem GroundTheory.PAdicHodge.ACris.iota_algebraMap (w : AInf K p) :
    iota K p (algebraMap (AInf K p) (ACris K p) w) = wittToBDeRhamPlus (normInteger K) p w := by sorry
