-- Prove2me | Theorems.Thm_GlobalTheory_DvrModel_existsUnique_gen
-- name    : GlobalTheory.DvrModel.existsUnique_gen
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:59:28.889877+00:00
-- url     : https://prove2.me/theorems/24397a73-302c-487e-a0d6-ff9023698836
-- title:
--   Dvr Model: exists Unique gen
-- statement:
--   The Dvr Model construction uses the exists Unique gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L219-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L219-L248

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

theorem GlobalTheory.DvrModel.existsUnique_gen {e : Spec (.of V) ⟶ H} (he : e ≫ f = 𝟙 _)
    {eK : Spec (.of K) ⟶ HK} (heK : eK ≫ j = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ e)
    {L : LB H} (hL : L.IsLB) (r : LB.Gen (L.pull j)) (hr : r.IsGen) (ρ : LB.Gen (L.pull e))
    (hρ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ r eK)
      (LB.pullGen L _ _ ρ (Spec.map (CommRingCat.ofHom (algebraMap V K))))) :
    ∃! r' : LB.Gen L, r'.IsGen ∧ LB.genPull L r' j = r := by sorry
