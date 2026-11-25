-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_exists_surjective_chart
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.exists_surjective_chart
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:36.902439+00:00
-- url     : https://prove2.me/theorems/c53f236f-37de-49fe-b136-671429bf28d4
-- title:
--   Proj Space: exists surjective chart
-- statement:
--   The Proj Space construction uses the exists surjective chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ChowLocal.lean#L29-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ChowLocal.lean#L29-L49

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveSpaceChart
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ChowLocal
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
variable {A : Type u} [CommRing A]

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.exists_surjective_chart {B : Type u} [CommRing B] (ρ : A →+* B) (hρ : ρ.FiniteType) :
    ∃ (n : ℕ) (g : Chart A (0 : Fin (n + 1)) →+* B), Function.Surjective g ∧
      g.comp (chartStructureMap n) = ρ := by sorry
