-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_bd
-- name    : GroundTheory.Arith.SchemeCoh.bd_bd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:13.479105+00:00
-- url     : https://prove2.me/theorems/b9204569-b20a-42c1-9b0d-49b38ac85603
-- title:
--   Scheme Coh: bd bd
-- statement:
--   The Scheme Coh construction uses the bd bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L47-L49

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

theorem GroundTheory.Arith.SchemeCoh.bd_bd (n : ℕ) (c : Chain ι (n + 2)) : bd n (bd (n + 1) c) = 0 := by sorry
