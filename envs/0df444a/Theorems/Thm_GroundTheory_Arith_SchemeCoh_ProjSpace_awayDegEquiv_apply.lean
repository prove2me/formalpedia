-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_awayDegEquiv_apply
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.awayDegEquiv_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:12:51.932631+00:00
-- url     : https://prove2.me/theorems/73bf44a1-f527-4913-b9e1-e6590ef2469d
-- title:
--   Proj Space: away Deg Equiv apply
-- statement:
--   The Proj Space construction uses the away Deg Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjCechModel.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjCechModel.lean#L37-L38

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

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.awayDegEquiv_apply {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (k : ℤ) (z) :
    (awayDegEquiv (A := A) i k z).1 = awayToLaurent i z.1 := by sorry

attribute [defeq] GroundTheory.Arith.SchemeCoh.ProjSpace.awayDegEquiv_apply
