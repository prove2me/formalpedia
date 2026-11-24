-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_ocone_add_ocone_bd
-- name    : GroundTheory.Arith.SchemeCoh.bd_ocone_add_ocone_bd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:23.042066+00:00
-- url     : https://prove2.me/theorems/b50fba5d-fc27-4ab4-933c-1945cbf68157
-- title:
--   Scheme Coh: bd ocone add ocone bd
-- statement:
--   The Scheme Coh construction uses the bd ocone add ocone bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L190-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L190-L222

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

theorem GroundTheory.Arith.SchemeCoh.bd_ocone_add_ocone_bd (n : ℕ) (s : ι) {c : Chain ι (n + 1)}
    (hc : c ∈ Finsupp.supported ℤ ℤ (ordFrom s)) :
    bd (n + 1) (ocone s c) + ocone s (bd n c) = c := by sorry
