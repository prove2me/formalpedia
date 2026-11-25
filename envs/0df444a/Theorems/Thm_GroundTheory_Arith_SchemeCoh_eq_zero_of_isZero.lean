-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_eq_zero_of_isZero
-- name    : GroundTheory.Arith.SchemeCoh.eq_zero_of_isZero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:08:03.035546+00:00
-- url     : https://prove2.me/theorems/cf6948b1-08a7-4f22-92dd-a302857937b1
-- title:
--   Scheme Coh: eq zero of is Zero
-- statement:
--   The Scheme Coh construction uses the eq zero of is Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/Support.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/Support.lean#L52-L54

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

theorem GroundTheory.Arith.SchemeCoh.eq_zero_of_isZero {F : X.Modules} (hF : IsZero F) (U : X.Opens) (s : Γ(F, U)) : s = 0 := by sorry
