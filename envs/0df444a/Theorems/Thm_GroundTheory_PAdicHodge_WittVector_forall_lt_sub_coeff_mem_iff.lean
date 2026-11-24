-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittVector_forall_lt_sub_coeff_mem_iff
-- name    : GroundTheory.PAdicHodge.WittVector.forall_lt_sub_coeff_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:59.90036+00:00
-- url     : https://prove2.me/theorems/b91a8964-ec7a-4eea-bcb7-1a671a6b0579
-- title:
--   Witt Vector: forall lt sub coeff mem iff
-- statement:
--   The Witt Vector construction uses the forall lt sub coeff mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L15-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L15-L33

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

theorem GroundTheory.PAdicHodge.WittVector.forall_lt_sub_coeff_mem_iff (J : Ideal R) (n : ℕ) (x y : WittVector p R) :
    (∀ i < n, x.coeff i - y.coeff i ∈ J) ↔ ∀ i < n, (x - y).coeff i ∈ J := by sorry
