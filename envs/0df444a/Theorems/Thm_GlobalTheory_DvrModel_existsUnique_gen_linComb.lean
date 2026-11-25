-- Prove2me | Theorems.Thm_GlobalTheory_DvrModel_existsUnique_gen_linComb
-- name    : GlobalTheory.DvrModel.existsUnique_gen_linComb
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:03.390461+00:00
-- url     : https://prove2.me/theorems/305fed1a-0e92-593c-ab21-50342329dadb
-- title:
--   Dvr Model: exists Unique gen lin Comb
-- statement:
--   The Dvr Model construction uses the exists Unique gen lin Comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L250-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L250-L276

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

theorem GlobalTheory.DvrModel.existsUnique_gen_linComb {e : Spec (.of V) ⟶ H} (he : e ≫ f = 𝟙 _)
    {eK : Spec (.of K) ⟶ HK} (heK : eK ≫ j = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ e)
    {X : Scheme.{u}} {L : LB X} (hL : L.IsLB) {κ : Type u} [Fintype κ] (φ : κ → (H ⟶ X))
    (ε : κ → ℤ) (r : LB.Gen (LB.LinComb L (fun k ↦ j ≫ φ k) ε)) (hr : r.IsGen) (a₀ : κ → L.ι)
    (h₀ : ⊤ ≤ e ⁻¹ᵁ LB.wchart L φ a₀) (h₀' : ⊤ ≤ eK ⁻¹ᵁ LB.wchart L (fun k ↦ j ≫ φ k) a₀)
    (u : Vˣ) (hu : eK.appLE _ ⊤ h₀' (LB.ts r a₀ : Γ(HK, LB.wchart L (fun k ↦ j ≫ φ k) a₀)) =
      (Scheme.ΓSpecIso (.of K)).inv (algebraMap V K u)) :
    ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L φ ε c j = r := by sorry
