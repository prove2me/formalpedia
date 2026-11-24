-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_inter_stdOpen
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.inter_stdOpen
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:23:45.243367+00:00
-- url     : https://prove2.me/theorems/7262f1a9-c82b-43ac-bba7-0d654299619f
-- title:
--   Proj Space: inter std Open
-- statement:
--   The Proj Space construction uses the inter std Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjSpace.lean#L50-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjSpace.lean#L50-L61

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
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
open ProjSpace
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.inter_stdOpen {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) :
    inter (X := (projectiveSpace A n).toTopCat) (stdOpen A n) i =
      Proj.basicOpen (grading A n) (xprod i) := by sorry
