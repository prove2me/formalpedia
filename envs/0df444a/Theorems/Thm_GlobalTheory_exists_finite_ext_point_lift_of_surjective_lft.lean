-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_ext_point_lift_of_surjective_lft
-- name    : GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:58.420795+00:00
-- url     : https://prove2.me/theorems/8503c731-5fa5-4da8-ac90-cc02a242c437
-- title:
--   Global Theory: exists finite ext point lift of surjective lft
-- statement:
--   The Global Theory construction uses the exists finite ext point lift of surjective lft property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteExtPointLiftOfSurjectiveLocFinType.lean#L8-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteExtPointLiftOfSurjectiveLocFinType.lean#L8-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteExtPointLiftOfSurjectiveLocFinType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory

theorem GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft :
    ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), LocallyOfFiniteType π → Function.Surjective π →
      ∀ (K : Type) [Field K] (x : Sp K ⟶ X),
        ∃ (K' : Type) (_ : Field K') (σ : K →+* K') (y : Sp K' ⟶ Y),
          σ.Finite ∧ y ≫ π = spMap σ ≫ x := by sorry
