-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_iotaQ_of
-- name    : GroundTheory.PAdicHodge.ACris.iotaQ_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:17.204252+00:00
-- url     : https://prove2.me/theorems/d88d7b9c-8533-4280-a3b8-a82950015766
-- title:
--   ACris: iota Q of
-- statement:
--   The ACris construction uses the iota Q of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdR.lean#L356-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdR.lean#L356-L359

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

theorem GroundTheory.PAdicHodge.ACris.iotaQ_of (m : ℕ) (y : ACrisZero K p) :
    iotaQ K p m (_root_.AdicCompletion.of _ _ y) = Ideal.Quotient.mk (kerAway K p ^ m) (y : 𝔸) := by sorry
