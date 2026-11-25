-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_map_chartAlgebraMap
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.map_chartAlgebraMap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:34:55.55972+00:00
-- url     : https://prove2.me/theorems/575a1588-171b-5b84-ab05-4bb45aea60b4
-- title:
--   Proj Space: map chart Algebra Map
-- statement:
--   The Proj Space construction uses the map chart Algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjBaseChange.lean#L87-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjBaseChange.lean#L87-L95

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveSpaceChart
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjBaseChange
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
open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)
variable {A B n}

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.map_chartAlgebraMap (j : Fin (n + 1)) (a : A) :
    Away.map (gradedMap A B n) (X j) (chartAlgebraMap A (X j) a) =
      chartAlgebraMap B (gradedMap A B n (X j)) (algebraMap A B a) := by sorry
