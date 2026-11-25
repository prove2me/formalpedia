-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_bijective_app_of_factor
-- name    : GroundTheory.Arith.SchemeCoh.bijective_app_of_factor
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:47:27.55628+00:00
-- url     : https://prove2.me/theorems/73b3fd7f-db5d-5ec2-b0ae-7f75f9e0505d
-- title:
--   Scheme Coh: bijective app of factor
-- statement:
--   The Scheme Coh construction uses the bijective app of factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/SectionTensor.lean#L15-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/SectionTensor.lean#L15-L72

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_RestrictTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_SectionTensor
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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory TensorProduct
universe u
noncomputable section
variable {X : Scheme.{u}}

theorem GroundTheory.Arith.SchemeCoh.bijective_app_of_factor {A B : X.Modules} (φ : A ⟶ B) {P : PMod X}
    (p : (preMod X).obj A ⟶ P) (q : P ⟶ (preMod X).obj B)
    (hq : ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj q)
    (hφ : (preMod X).map φ = p ≫ q) {W : X.Opens}
    (hp : ∀ V ≤ W, Function.Bijective (p.app (op V))) :
    ∀ V ≤ W, Function.Bijective (φ.app V) := by sorry
