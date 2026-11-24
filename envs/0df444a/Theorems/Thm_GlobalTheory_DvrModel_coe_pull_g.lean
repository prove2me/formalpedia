-- Prove2me | Theorems.Thm_GlobalTheory_DvrModel_coe_pull_g
-- name    : GlobalTheory.DvrModel.coe_pull_g
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:57:43.137074+00:00
-- url     : https://prove2.me/theorems/3b1d97dc-7498-4bba-9bbb-37bb988042c9
-- title:
--   Dvr Model: coe pull g
-- statement:
--   The Dvr Model construction uses the coe pull g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L167-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L167-L171

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

theorem GlobalTheory.DvrModel.coe_pull_g {X Y : Scheme.{u}} (L : LB X) (φ : Y ⟶ X) (a b : PUnit → L.ι) :
    ((L.pull φ).g a b : Γ(Y, (L.pull φ).U a ⊓ (L.pull φ).U b)) =
      φ.appLE (L.U (a ⟨⟩) ⊓ L.U (b ⟨⟩)) _ (inf_le_inf (pull_U L φ a).le (pull_U L φ b).le)
        (L.g (a ⟨⟩) (b ⟨⟩) : Γ(X, L.U (a ⟨⟩) ⊓ L.U (b ⟨⟩))) := by sorry
