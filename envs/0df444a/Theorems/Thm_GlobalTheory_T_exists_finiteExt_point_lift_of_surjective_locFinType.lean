-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finiteExt_point_lift_of_surjective_locFinType
-- name    : GlobalTheory.T.exists_finiteExt_point_lift_of_surjective_locFinType
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:09.159544+00:00
-- url     : https://prove2.me/theorems/58aeb799-bae8-4dd4-88a2-fd95276797f9
-- title:
--   T: exists finite Ext point lift of surjective loc Fin Type
-- statement:
--   The T construction uses the exists finite Ext point lift of surjective loc Fin Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteExtPointLiftOfSurjectiveLocFinTypeStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteExtPointLiftOfSurjectiveLocFinTypeStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteExtPointLiftOfSurjectiveLocFinType
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteExtPointLiftOfSurjectiveLocFinTypeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finiteExt_point_lift_of_surjective_locFinType : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), LocallyOfFiniteType π → Function.Surjective π → ∀ (K : Type) [Field K] (x : Sp K ⟶ X), ∃ (K' : Type) (_ : Field K') (σ : K →+* K') (y : Sp K' ⟶ Y), σ.Finite ∧ y ≫ π = spMap σ ≫ x := by sorry
