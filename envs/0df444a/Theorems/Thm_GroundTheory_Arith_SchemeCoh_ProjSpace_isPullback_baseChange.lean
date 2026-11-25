-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_isPullback_baseChange
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.isPullback_baseChange
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:28:43.860355+00:00
-- url     : https://prove2.me/theorems/804e3905-76f7-58b7-9aa9-9938e8b366e5
-- title:
--   Proj Space: is Pullback base Change
-- statement:
--   The Proj Space construction uses the is Pullback base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjBaseChange.lean#L161-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjBaseChange.lean#L161-L180

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
variable (A B n)

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.isPullback_baseChange :
    IsPullback (baseChangeMap A B n) (toSpecBase B n) (toSpecBase A n)
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by sorry
