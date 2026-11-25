-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_shortExact_abShortComplex
-- name    : GroundTheory.Arith.SchemeCoh.shortExact_abShortComplex
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:53:01.924349+00:00
-- url     : https://prove2.me/theorems/949ff6d4-dea0-5dd3-93fe-f876721fa05e
-- title:
--   Scheme Coh: short Exact ab Short Complex
-- statement:
--   The Scheme Coh construction uses the short Exact ab Short Complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ModulesAbExact.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ModulesAbExact.lean#L71-L73

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

theorem GroundTheory.Arith.SchemeCoh.shortExact_abShortComplex {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (abShortComplex S).ShortExact := by sorry
