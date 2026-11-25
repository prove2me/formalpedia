-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_cone_add_cone_bd
-- name    : GroundTheory.Arith.SchemeCoh.bd_cone_add_cone_bd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:13.185467+00:00
-- url     : https://prove2.me/theorems/949bffe0-479b-4f07-96df-86a813366e75
-- title:
--   Scheme Coh: bd cone add cone bd
-- statement:
--   The Scheme Coh construction uses the bd cone add cone bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L119-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L119-L132

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

theorem GroundTheory.Arith.SchemeCoh.bd_cone_add_cone_bd (n : ℕ) (s : ι) (c : Chain ι (n + 1)) :
    bd (n + 1) (cone s c) + cone s (bd n c) = c := by sorry
