-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_iota_of
-- name    : GroundTheory.PAdicHodge.ACris.iota_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:27.394451+00:00
-- url     : https://prove2.me/theorems/3164b591-29aa-56c2-8d6d-9ff8f76b36ff
-- title:
--   ACris: iota of
-- statement:
--   The ACris construction uses the iota of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdR.lean#L394-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdR.lean#L394-L399

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

theorem GroundTheory.PAdicHodge.ACris.iota_of (y : ACrisZero K p) :
    iota K p (_root_.AdicCompletion.of _ _ y) = toBDeRhamPlus (normInteger K) p (y : 𝔸) := by sorry
