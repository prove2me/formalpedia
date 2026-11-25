-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_shortExact_map_toSheaf
-- name    : GroundTheory.Arith.SchemeCoh.shortExact_map_toSheaf
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:02:34.80889+00:00
-- url     : https://prove2.me/theorems/6a288dd4-9c2c-54de-8c17-4307392ed7ff
-- title:
--   Scheme Coh: short Exact map to Sheaf
-- statement:
--   The Scheme Coh construction uses the short Exact map to Sheaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ModulesAbExact.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ModulesAbExact.lean#L62-L69

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Linear
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_ModulesAbExact
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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
universe u
noncomputable section
variable {X : Scheme.{u}}

theorem GroundTheory.Arith.SchemeCoh.shortExact_map_toSheaf {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)}
    (hS : S.ShortExact) : (S.map (SheafOfModules.toSheaf X.ringCatSheaf)).ShortExact := by sorry
