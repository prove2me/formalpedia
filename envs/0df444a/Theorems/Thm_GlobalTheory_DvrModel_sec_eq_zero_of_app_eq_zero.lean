-- Prove2me | Theorems.Thm_GlobalTheory_DvrModel_sec_eq_zero_of_app_eq_zero
-- name    : GlobalTheory.DvrModel.sec_eq_zero_of_app_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:59:13.492826+00:00
-- url     : https://prove2.me/theorems/03e841c5-f26c-4fbe-98c7-f475982bd6e6
-- title:
--   Dvr Model: sec eq zero of app eq zero
-- statement:
--   The Dvr Model construction uses the sec eq zero of app eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L292-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L292-L311

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

theorem GlobalTheory.DvrModel.sec_eq_zero_of_app_eq_zero (hϖ : Irreducible ϖ) {L : LB H} (hL : L.IsLB) (s : L.Sec)
    {Z : ℕ → Scheme.{u}} {k : ∀ n, Z n ⟶ H}
    {p : ∀ n, Z n ⟶ Spec (.of (V ⧸ Ideal.span {ϖ ^ n}))}
    (hZ : ∀ n, IsPullback (k n) (p n) f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ϖ ^ n})))))
    (h : ∀ a n, (k n).app (L.U a) (s.f a) = 0) (a : L.ι) : s.f a = 0 := by sorry
