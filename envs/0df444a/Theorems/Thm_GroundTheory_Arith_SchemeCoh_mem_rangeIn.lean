-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_rangeIn
-- name    : GroundTheory.Arith.SchemeCoh.mem_rangeIn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:06.734116+00:00
-- url     : https://prove2.me/theorems/6a4d0ed7-14a4-4c52-becf-c99039337902
-- title:
--   Scheme Coh: mem range In
-- statement:
--   The Scheme Coh construction uses the mem range In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L86-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L86-L87

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

theorem GroundTheory.Arith.SchemeCoh.mem_rangeIn {n : ℕ} {S : Set ι} {j : Fin (n + 1) → ι} : j ∈ rangeIn S ↔ Set.range j ⊆ S := by sorry
