-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_mem_rangeIn
-- name    : GroundTheory.Arith.SchemeCoh.bd_mem_rangeIn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:25.569169+00:00
-- url     : https://prove2.me/theorems/84896338-7806-4f7f-a8fb-c2c24dc45491
-- title:
--   Scheme Coh: bd mem range In
-- statement:
--   The Scheme Coh construction uses the bd mem range In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L103-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L103-L110

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

theorem GroundTheory.Arith.SchemeCoh.bd_mem_rangeIn {n : ℕ} {S : Set ι} {c : Chain ι (n + 1)}
    (hc : c ∈ Finsupp.supported ℤ ℤ (rangeIn S)) :
    bd n c ∈ Finsupp.supported ℤ ℤ (rangeIn S) := by sorry
