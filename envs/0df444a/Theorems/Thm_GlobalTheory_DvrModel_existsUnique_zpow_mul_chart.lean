-- Prove2me | Theorems.Thm_GlobalTheory_DvrModel_existsUnique_zpow_mul_chart
-- name    : GlobalTheory.DvrModel.existsUnique_zpow_mul_chart
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:59:01.924096+00:00
-- url     : https://prove2.me/theorems/1037191a-6af2-4382-8f8d-b59d34bbc0e3
-- title:
--   Dvr Model: exists Unique zpow mul chart
-- statement:
--   The Dvr Model construction uses the exists Unique zpow mul chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L313-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L313-L338

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
variable [Flat f] [LocallyOfFiniteType f] [IsIntegral HK] [IsIntegral Hs]
  (hK : IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K))))
  (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V))))
include hK hs

theorem GlobalTheory.DvrModel.existsUnique_zpow_mul_chart (hϖ : Irreducible ϖ) {ι : Type v} {U : ι → H.Opens}
    {g : ∀ a b, Γ(H, U a ⊓ U b)} {W : ι → HK.Opens} (hW : ∀ a, W a = j ⁻¹ᵁ U a)
    (hU : ∀ x : H, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b)) {r : ∀ a, Γ(HK, W a)}
    (hr : ∀ a b, HK.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        HK.presheaf.map (homOfLE inf_le_right).op (r b))
    (hr0 : ∃ a, r a ≠ 0) :
    ∃! n : ℤ, ∃ s : ∀ a, Γ(H, U a),
      (∀ a b, H.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * H.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      (∀ a, j.appLE (U a) (W a) (hW a).le (s a) =
        HK.presheaf.map (homOfLE le_top).op cst[fK, K, algebraMap V K ϖ ^ n] * r a) ∧
      ∃ a, ∃ x, f x = closedPoint V ∧ x ∈ H.basicOpen (s a) := by sorry
