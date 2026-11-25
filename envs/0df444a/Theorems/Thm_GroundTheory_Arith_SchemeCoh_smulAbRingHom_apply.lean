-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_smulAbRingHom_apply
-- name    : GroundTheory.Arith.SchemeCoh.smulAbRingHom_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:57:51.011554+00:00
-- url     : https://prove2.me/theorems/745da5fb-a18a-4578-a888-90521e154104
-- title:
--   Scheme Coh: smul Ab Ring Hom apply
-- statement:
--   The Scheme Coh construction uses the smul Ab Ring Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Linear.lean#L113-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Linear.lean#L113-L114

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

theorem GroundTheory.Arith.SchemeCoh.smulAbRingHom_apply (F : X.Modules) (r : Γ(X, ⊤)) :
    smulAbRingHom F r = (SheafOfModules.toSheaf X.ringCatSheaf).map (smulHom F r) := by sorry
