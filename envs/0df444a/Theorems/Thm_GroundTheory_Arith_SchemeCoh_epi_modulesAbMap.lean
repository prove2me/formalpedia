-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_epi_modulesAbMap
-- name    : GroundTheory.Arith.SchemeCoh.epi_modulesAbMap
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:02:29.390953+00:00
-- url     : https://prove2.me/theorems/998d05ae-c384-5a65-b9ec-73822ad7c87c
-- title:
--   Scheme Coh: epi modules Ab Map
-- statement:
--   The Scheme Coh construction uses the epi modules Ab Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ModulesAbExact.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ModulesAbExact.lean#L53-L54

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

theorem GroundTheory.Arith.SchemeCoh.epi_modulesAbMap {F G : X.Modules} (φ : F ⟶ G) [hφ : Epi φ] : Epi (modulesAbMap φ) := by sorry
