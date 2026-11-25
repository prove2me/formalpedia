-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_cone_mem_rangeIn
-- name    : GroundTheory.Arith.SchemeCoh.cone_mem_rangeIn
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:31.166152+00:00
-- url     : https://prove2.me/theorems/4f31a5c7-bbf1-4aaf-b9ef-3d4c6fcf6618
-- title:
--   Scheme Coh: cone mem range In
-- statement:
--   The Scheme Coh construction uses the cone mem range In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L134-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L134-L143

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory
universe w
variable {ι : Type w}

theorem GroundTheory.Arith.SchemeCoh.cone_mem_rangeIn {n : ℕ} {S : Set ι} {s : ι} (hs : s ∈ S) {c : Chain ι n}
    (hc : c ∈ Finsupp.supported ℤ ℤ (rangeIn S)) :
    cone s c ∈ Finsupp.supported ℤ ℤ (rangeIn S) := by sorry
