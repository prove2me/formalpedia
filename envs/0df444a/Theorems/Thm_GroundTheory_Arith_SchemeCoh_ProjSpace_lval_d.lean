-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_d
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.lval_d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:12:42.342889+00:00
-- url     : https://prove2.me/theorems/19a58543-628f-44e3-95c4-8d6da75376c3
-- title:
--   Proj Space: lval d
-- statement:
--   The Proj Space construction uses the lval d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjCechModel.lean#L131-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjCechModel.lean#L131-L143

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

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.lval_d {k : ℤ} {p : ℕ} (σ : Cochain (twistAb A n k) (cover A n) p)
    (i : Fin (p + 2) → Fin (n + 1)) :
    lval (d _ _ p σ) i = ∑ a : Fin (p + 2), ((-1 : ℤ) ^ (a : ℕ)) • lval σ (i ∘ a.succAbove) := by sorry
