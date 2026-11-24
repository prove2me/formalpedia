-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ocone_single_of_not_lt
-- name    : GroundTheory.Arith.SchemeCoh.ocone_single_of_not_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:45.272343+00:00
-- url     : https://prove2.me/theorems/3fd59fe3-4546-4d2d-bc8b-4d4b7fbde0b2
-- title:
--   Scheme Coh: ocone single of not lt
-- statement:
--   The Scheme Coh construction uses the ocone single of not lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L185-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L185-L188

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

theorem GroundTheory.Arith.SchemeCoh.ocone_single_of_not_lt {n : ℕ} {s : ι} {i : Fin (n + 1) → ι} (h : ¬ s < i 0) (z : ℤ) :
    ocone s (Finsupp.single i z) = 0 := by sorry
