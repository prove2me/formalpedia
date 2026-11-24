-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_ordFrom
-- name    : GroundTheory.Arith.SchemeCoh.mem_ordFrom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:18.886817+00:00
-- url     : https://prove2.me/theorems/76f40121-7cf7-4938-be42-f566b692683b
-- title:
--   Scheme Coh: mem ord From
-- statement:
--   The Scheme Coh construction uses the mem ord From property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L166-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L166-L167

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

theorem GroundTheory.Arith.SchemeCoh.mem_ordFrom {n : ℕ} {s : ι} {j : Fin (n + 1) → ι} : j ∈ ordFrom s ↔ StrictMono j ∧ s ≤ j 0 := by sorry
