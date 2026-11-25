-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittVector_coeff_mem_of_mem_span_teichmuller
-- name    : GroundTheory.PAdicHodge.WittVector.coeff_mem_of_mem_span_teichmuller
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:21.397079+00:00
-- url     : https://prove2.me/theorems/9d4c035b-2097-468b-809f-286bd4a2528f
-- title:
--   Witt Vector: coeff mem of mem span teichmuller
-- statement:
--   The Witt Vector construction uses the coeff mem of mem span teichmuller property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L45-L49

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
variable [CharP R p]

theorem GroundTheory.PAdicHodge.WittVector.coeff_mem_of_mem_span_teichmuller {b : R} {J : Ideal R} (hb : b ∈ J)
    {y : WittVector p R} (hy : y ∈ Ideal.span {teichmuller p b}) (i : ℕ) : y.coeff i ∈ J := by sorry
