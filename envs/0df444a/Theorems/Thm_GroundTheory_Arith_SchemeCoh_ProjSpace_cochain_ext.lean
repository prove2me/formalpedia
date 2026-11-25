-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_cochain_ext
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.cochain_ext
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:11:32.321934+00:00
-- url     : https://prove2.me/theorems/a8f7aeab-fb7f-4b4e-ad80-678dd887b705
-- title:
--   Proj Space: cochain ext
-- statement:
--   The Proj Space construction uses the cochain ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjCechModel.lean#L99-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjCechModel.lean#L99-L104

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

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.cochain_ext {k : ℤ} {p : ℕ} {σ τ : Cochain (twistAb A n k) (cover A n) p}
    (h : ∀ i, lval σ i = lval τ i) : σ = τ := by sorry
