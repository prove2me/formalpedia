-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_ordIn
-- name    : GroundTheory.Arith.SchemeCoh.mem_ordIn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:12.61824+00:00
-- url     : https://prove2.me/theorems/3f7090ce-cd1e-4e87-bc64-7db33367c544
-- title:
--   Scheme Coh: mem ord In
-- statement:
--   The Scheme Coh construction uses the mem ord In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L160-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L160-L162

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
variable [LinearOrder ι]

theorem GroundTheory.Arith.SchemeCoh.mem_ordIn {n : ℕ} {S : Set ι} {j : Fin (n + 1) → ι} :
    j ∈ ordIn S ↔ StrictMono j ∧ Set.range j ⊆ S := by sorry
