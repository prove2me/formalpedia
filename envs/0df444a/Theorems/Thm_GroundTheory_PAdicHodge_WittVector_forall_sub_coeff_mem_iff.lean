-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittVector_forall_sub_coeff_mem_iff
-- name    : GroundTheory.PAdicHodge.WittVector.forall_sub_coeff_mem_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:59.478311+00:00
-- url     : https://prove2.me/theorems/7d1310e4-abc3-47c5-855f-fe943bda6138
-- title:
--   Witt Vector: forall sub coeff mem iff
-- statement:
--   The Witt Vector construction uses the forall sub coeff mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L35-L41

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
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
open WittVector Filter Topology
open GroundTheory GroundTheory.PAdicHodge
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

theorem GroundTheory.PAdicHodge.WittVector.forall_sub_coeff_mem_iff (J : Ideal R) (x y : WittVector p R) :
    (∀ i, x.coeff i - y.coeff i ∈ J) ↔ ∀ i, (x - y).coeff i ∈ J := by sorry
