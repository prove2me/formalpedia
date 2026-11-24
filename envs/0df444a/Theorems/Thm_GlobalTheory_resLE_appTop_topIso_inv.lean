-- Prove2me | Theorems.Thm_GlobalTheory_resLE_appTop_topIso_inv
-- name    : GlobalTheory.resLE_appTop_topIso_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:16:08.622123+00:00
-- url     : https://prove2.me/theorems/216031ee-c778-47b5-96b1-7d55335fdcef
-- title:
--   Global Theory: res LE app Top top Iso inv
-- statement:
--   The Global Theory construction uses the res LE app Top top Iso inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueDescendOfTorsionInvariant.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueDescendOfTorsionInvariant.lean#L94-L98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.resLE_appTop_topIso_inv {X Y : Scheme.{0}} (t : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ t ⁻¹ᵁ U) (g : Γ(Y, U)) :
    (t.resLE U V e).appTop.hom (U.topIso.inv.hom g) = V.topIso.inv.hom ((t.appLE U V e).hom g) := by sorry
