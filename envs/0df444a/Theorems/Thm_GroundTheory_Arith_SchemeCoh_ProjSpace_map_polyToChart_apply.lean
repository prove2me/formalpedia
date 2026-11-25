-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_map_polyToChart_apply
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.map_polyToChart_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:35:01.493039+00:00
-- url     : https://prove2.me/theorems/ba143d49-db9a-5cd0-8119-5ae5ca5bc779
-- title:
--   Proj Space: map poly To Chart apply
-- statement:
--   The Proj Space construction uses the map poly To Chart apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjBaseChange.lean#L124-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjBaseChange.lean#L124-L127

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

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.map_polyToChart_apply (j : Fin (n + 1)) (p : MvPolynomial {i // i ≠ j} A) :
    Away.map (gradedMap A B n) (X j) (polyToChart A j p) =
      (awayCongr B n (gradedMap_X A B n j)).symm (polyToChart B j (MvPolynomial.map (algebraMap A B) p)) := by sorry
