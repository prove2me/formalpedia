-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_lin_rho_zero
-- name    : GroundTheory.Arith.SchemeCoh.lin_rho_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:45.613593+00:00
-- url     : https://prove2.me/theorems/47f712e5-bac5-4cc4-a51c-767d5a56f797
-- title:
--   Scheme Coh: lin rho zero
-- statement:
--   The Scheme Coh construction uses the lin rho zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L285-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L285-L289

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

theorem GroundTheory.Arith.SchemeCoh.lin_rho_zero (c : Chain ι 0) : lin (rho (ι := ι) 0) c = c := by sorry
