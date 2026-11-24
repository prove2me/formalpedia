-- Prove2me | Theorems.Thm_GlobalTheory_DvrModel_existsUnique_zpow_mul_sec
-- name    : GlobalTheory.DvrModel.existsUnique_zpow_mul_sec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:59:04.222565+00:00
-- url     : https://prove2.me/theorems/c5c710a2-1bb0-4209-a741-2f221d0d1de2
-- title:
--   Dvr Model: exists Unique zpow mul sec
-- statement:
--   The Dvr Model construction uses the exists Unique zpow mul sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L340-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L340-L356

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

theorem GlobalTheory.DvrModel.existsUnique_zpow_mul_sec (hϖ : Irreducible ϖ) {L : LB H} (hL : L.IsLB)
    (r : (L.pull j).Sec) (hr0 : ∃ a, r.f a ≠ 0) :
    ∃! n : ℤ, ∃ s : L.Sec,
      (∀ a : PUnit → L.ι, j.appLE (L.U (a ⟨⟩)) ((L.pull j).U a) (pull_U L j a).le (s.f (a ⟨⟩)) =
        HK.presheaf.map (homOfLE le_top).op cst[fK, K, algebraMap V K ϖ ^ n] * r.f a) ∧
      ∃ a, ∃ x, f x = closedPoint V ∧ x ∈ H.basicOpen (s.f a) := by sorry
