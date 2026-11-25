-- Prove2me | Theorems.Thm_GlobalTheory_finite_algebra_split_local
-- name    : GlobalTheory.finite_algebra_split_local
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:43:51.749024+00:00
-- url     : https://prove2.me/theorems/461cc272-4a0f-499e-be2e-8c78810f0a28
-- title:
--   Global Theory: finite algebra split local
-- statement:
--   The Global Theory construction uses the finite algebra split local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FiniteAlgebraSplitLocal.lean#L77-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FiniteAlgebraSplitLocal.lean#L77-L178

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FiniteAlgebraSplitLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.finite_algebra_split_local :
  (∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Finite (A →ₐ[O] O)],
    (∀ f : A, (∀ φ : A →ₐ[O] O, φ f = 0) → f = 0) →
    ∃ (n : ℕ) (ε : Fin n → A), CompleteOrthogonalIdempotents ε ∧ ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - ε i})) := by sorry
