-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_ofL
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.lval_ofL
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:11:19.729357+00:00
-- url     : https://prove2.me/theorems/20731182-20ae-4364-893c-e1507cce2fbf
-- title:
--   Proj Space: lval of L
-- statement:
--   The Proj Space construction uses the lval of L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjCechModel.lean#L122-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjCechModel.lean#L122-L124

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

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.lval_ofL {k : ℤ} {p : ℕ} (f : ∀ i : Fin (p + 1) → Fin (n + 1), LDeg A (Set.range i) k)
    (i) : lval (ofL f) i = (f i).1 := by sorry
