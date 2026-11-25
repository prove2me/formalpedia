-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_isPushout_chart
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.isPushout_chart
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:35:36.265488+00:00
-- url     : https://prove2.me/theorems/4e42bcca-4458-43ea-8e30-bdda58af25ed
-- title:
--   Proj Space: is Pushout chart
-- statement:
--   The Proj Space construction uses the is Pushout chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjBaseChange.lean#L131-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjBaseChange.lean#L131-L148

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
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.isPushout_chart (j : Fin (n + 1)) :
    IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (chartAlgebraMap A (X j)))
      (CommRingCat.ofHom (chartAlgebraMap B (gradedMap A B n (X j))))
      (CommRingCat.ofHom (Away.map (gradedMap A B n) (X j))) := by sorry
