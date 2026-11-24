-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isPullback_rees
-- name    : GroundTheory.Arith.SchemeCoh.isPullback_rees
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:02.28272+00:00
-- url     : https://prove2.me/theorems/8372a87b-318d-47d3-b749-59acfbfd313f
-- title:
--   Scheme Coh: is Pullback rees
-- statement:
--   The Scheme Coh construction uses the is Pullback rees property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesScheme.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesScheme.lean#L30-L32

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesSubmodule
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackGamma
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesScheme
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
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
noncomputable section
variable {A : Type u} [CommRing A] (I : Ideal A) (X : Scheme.{u}) [X.Over (Spec (.of A))]

theorem GroundTheory.Arith.SchemeCoh.isPullback_rees :
    IsPullback (reesPr I X) (reesSnd I X) (X ↘ Spec (.of A)) (reesStructure I) := by sorry
