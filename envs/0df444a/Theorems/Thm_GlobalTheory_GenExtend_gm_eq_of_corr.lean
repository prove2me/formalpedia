-- Prove2me | Theorems.Thm_GlobalTheory_GenExtend_gm_eq_of_corr
-- name    : GlobalTheory.GenExtend.gm_eq_of_corr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:16:50.009158+00:00
-- url     : https://prove2.me/theorems/a0a2c0b0-44e9-4791-908c-9032c3c97486
-- title:
--   Gen Extend: gm eq of corr
-- statement:
--   The Gen Extend construction uses the gm eq of corr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueGeneratorExtendDiscreteValuationRing.lean#L16-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueGeneratorExtendDiscreteValuationRing.lean#L16-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueGeneratorExtendDiscreteValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenExtend
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DvrModel

theorem GlobalTheory.GenExtend.gm_eq_of_corr {X Y Y' Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {φ' : I → (Y' ⟶ X)} {ε : I → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (r : Z ⟶ Y) (r' : Z ⟶ Y')
    (h : ∀ i, r ≫ φ i = r' ≫ φ' i)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t r) (LB.pullGen L _ _ t' r')) (z : Z)
    (a : I → L.ι) (ha : r z ∈ LB.wchart L φ a) (ha' : r' z ∈ LB.wchart L φ' a) :
    gm r z (LB.wchart L φ a) (t.s a) = gm r' z (LB.wchart L φ' a) (t'.s a) := by sorry
