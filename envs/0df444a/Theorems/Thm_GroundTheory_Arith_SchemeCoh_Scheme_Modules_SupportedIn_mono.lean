-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_Scheme_Modules_SupportedIn_mono
-- name    : GroundTheory.Arith.SchemeCoh.Scheme.Modules.SupportedIn.mono
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:58:37.932986+00:00
-- url     : https://prove2.me/theorems/82a4cfe9-7f90-49e9-b97f-45c3dce3dc55
-- title:
--   Supported In: mono
-- statement:
--   The Supported In construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/Support.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/Support.lean#L20-L22

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_QcohLocal
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_Support
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
open GroundTheory.Arith.SchemeCoh.Scheme GroundTheory.Arith.SchemeCoh.Scheme.Modules GroundTheory.Arith.SchemeCoh.Scheme.Modules.SupportedIn

theorem GroundTheory.Arith.SchemeCoh.Scheme.Modules.SupportedIn.mono {F : X.Modules} {T T' : Set X} (h : Scheme.Modules.SupportedIn F T) (hT : T ⊆ T') :
    Scheme.Modules.SupportedIn F T' := by sorry
