-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_smulRingHom_apply
-- name    : GroundTheory.Arith.SchemeCoh.smulRingHom_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:53:04.8294+00:00
-- url     : https://prove2.me/theorems/3d42c932-4236-56d2-a2af-f61edcefeccb
-- title:
--   Scheme Coh: smul Ring Hom apply
-- statement:
--   The Scheme Coh construction uses the smul Ring Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Linear.lean#L96-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Linear.lean#L96-L96

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Linear
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
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits
universe w' w v u
variable {X : Scheme.{u}}

theorem GroundTheory.Arith.SchemeCoh.smulRingHom_apply (F : X.Modules) (r : Γ(X, ⊤)) : smulRingHom F r = smulHom F r := by sorry
