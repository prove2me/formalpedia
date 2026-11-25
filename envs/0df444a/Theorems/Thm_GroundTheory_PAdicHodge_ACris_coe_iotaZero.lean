-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_coe_iotaZero
-- name    : GroundTheory.PAdicHodge.ACris.coe_iotaZero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:08.039031+00:00
-- url     : https://prove2.me/theorems/eb3dcf25-08ac-402c-8489-896da8f09ab0
-- title:
--   ACris: coe iota Zero
-- statement:
--   The ACris construction uses the coe iota Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdR.lean#L337-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdR.lean#L337-L339

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

theorem GroundTheory.PAdicHodge.ACris.coe_iotaZero (m : ℕ) (y : ACrisZero K p) :
    (iotaZero K p m y : 𝔸 ⧸ kerAway K p ^ m) = Ideal.Quotient.mk (kerAway K p ^ m) (y : 𝔸) := by sorry
