-- Prove2me | Theorems.Thm_GlobalTheory_GenExtend_res_pullU_eq_of_corr
-- name    : GlobalTheory.GenExtend.res_pullU_eq_of_corr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:17:35.459632+00:00
-- url     : https://prove2.me/theorems/198cf2c6-b149-4331-b0dd-0b9b13b8f553
-- title:
--   Gen Extend: res pull U eq of corr
-- statement:
--   The Gen Extend construction uses the res pull U eq of corr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueGeneratorExtendDiscreteValuationRing.lean#L32-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueGeneratorExtendDiscreteValuationRing.lean#L32-L47

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

theorem GlobalTheory.GenExtend.res_pullU_eq_of_corr {X Y Y' Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {φ' : I → (Y' ⟶ X)} {ε : I → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (r : Z ⟶ Y) (r' : Z ⟶ Y')
    (h : ∀ i, r ≫ φ i = r' ≫ φ' i)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t r) (LB.pullGen L _ _ t' r'))
    (a : I → L.ι) {A : Z.Opens} (hA : A ≤ r ⁻¹ᵁ LB.wchart L φ a)
    (hA' : A ≤ r' ⁻¹ᵁ LB.wchart L φ' a) :
    r'.appLE (LB.wchart L φ' a) A hA' (LB.ts t' a : Γ(Y', LB.wchart L φ' a)ˣ) =
      r.appLE (LB.wchart L φ a) A hA (LB.ts t a : Γ(Y, LB.wchart L φ a)ˣ) := by sorry
