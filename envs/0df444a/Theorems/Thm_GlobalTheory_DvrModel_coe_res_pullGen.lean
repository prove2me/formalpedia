-- Prove2me | Theorems.Thm_GlobalTheory_DvrModel_coe_res_pullGen
-- name    : GlobalTheory.DvrModel.coe_res_pullGen
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:03:05.968385+00:00
-- url     : https://prove2.me/theorems/3238a487-8248-4819-b881-48ad1ebac8fa
-- title:
--   Dvr Model: coe res pull Gen
-- statement:
--   The Dvr Model construction uses the coe res pull Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L173-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L173-L179

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.DvrModel
open PrimeSection
variable {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {K : Type u} [Field K] [Algebra V K] [IsFractionRing V K] {ϖ : V}
  {H : Scheme.{u}} {f : H ⟶ Spec (.of V)}
  {HK : Scheme.{u}} {j : HK ⟶ H} {fK : HK ⟶ Spec (.of K)}
  {Hs : Scheme.{u}} {i : Hs ⟶ H} {fs : Hs ⟶ Spec (.of (ResidueField V))}
local notation "cst[" f ", " R ", " c "]" =>
  ConcreteCategory.hom (Scheme.Hom.appTop f)
    (ConcreteCategory.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of R))) c)

theorem GlobalTheory.DvrModel.coe_res_pullGen {X Y Z : Scheme.{u}} (L : LB X) {κ : Type u} [Fintype κ]
    (φ : κ → (Y ⟶ X)) (ε : κ → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (a : κ → L.ι)
    {A : Z.Opens} (hA : A ≤ LB.wchart L (fun k ↦ h ≫ φ k) a) :
    (res hA (LB.ts (LB.pullGen L φ ε c h) a) : Γ(Z, A)ˣ) =
      h.appLE (LB.wchart L φ a) A (hA.trans (LB.wchart_comp_le L h φ a))
        (LB.ts c a : Γ(Y, LB.wchart L φ a)ˣ) := by sorry
