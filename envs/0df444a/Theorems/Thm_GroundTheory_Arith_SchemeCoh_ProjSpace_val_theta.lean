-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_val_theta
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.val_theta
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:11:27.344931+00:00
-- url     : https://prove2.me/theorems/c11eed7c-287a-4923-b365-f9c6034e1350
-- title:
--   Proj Space: val theta
-- statement:
--   The Proj Space construction uses the val theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjCechModel.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjCechModel.lean#L70-L73

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
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
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.val_theta {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (k : ℤ) (ℓ : LDeg A (Set.range i) k)
    (x : inter (cover A n) i) :
    ProjTwist.val (theta i k ℓ) x =
      ProjTwist.locMap x.1 (nmem_of_mem_inter x) ((awayDegEquiv i k).symm ℓ).1 := by sorry
