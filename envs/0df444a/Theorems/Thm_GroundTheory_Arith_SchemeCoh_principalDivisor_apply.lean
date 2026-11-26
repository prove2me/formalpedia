-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_principalDivisor_apply
-- name    : GroundTheory.Arith.SchemeCoh.principalDivisor_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:52:25.467315+00:00
-- url     : https://prove2.me/theorems/887f1ec7-b32e-4092-9b29-939420d529f0
-- title:
--   Scheme Coh: principal Divisor apply
-- statement:
--   The Scheme Coh construction uses the principal Divisor apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/WeilDivisor.lean#L206-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/WeilDivisor.lean#L206-L207

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
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
open CategoryTheory AlgebraicGeometry IsDedekindDomain TopologicalSpace Topology
universe u
variable {X : Scheme.{u}}
variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]

theorem GroundTheory.Arith.SchemeCoh.principalDivisor_apply (f : (X.functionField)ˣ) (x : PrimeDivisor X) :
    principalDivisor (Additive.ofMul f) x = x.ord (f : X.functionField) := by sorry
