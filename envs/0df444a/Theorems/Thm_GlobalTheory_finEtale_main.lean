-- Prove2me | Theorems.Thm_GlobalTheory_finEtale_main
-- name    : GlobalTheory.finEtale_main
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:41:47.063144+00:00
-- url     : https://prove2.me/theorems/7b9e48a1-cf9e-5deb-8287-2f8b76a11dde
-- title:
--   Global Theory: fin Etale main
-- statement:
--   The Global Theory construction uses the fin Etale main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinEtaleFormallyUnramified.lean#L109-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinEtaleFormallyUnramified.lean#L109-L201

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinEtaleFormallyUnramified
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
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.finEtale_main :
    (∀ (C O A : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) [CommRing O]
      [Algebra O C], v.Integers O →
      ∀ [CommRing A] [Algebra O A] [Module.Free O A] [Module.Finite O A],
      (∀ φ φ' : A →ₐ[O] DualNumber C, (∀ a, (φ a).fst = (φ' a).fst) → φ = φ') →
      Finite (A →ₐ[O] O) ∧ (∀ f : A, (∀ φ : A →ₐ[O] O, φ f = 0) → f = 0) ∧
        Module.finrank O A = Nat.card (A →ₐ[O] O)) := by sorry
