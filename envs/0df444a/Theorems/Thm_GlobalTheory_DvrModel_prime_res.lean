-- Prove2me | Theorems.Thm_GlobalTheory_DvrModel_prime_res
-- name    : GlobalTheory.DvrModel.prime_res
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:57:00.391829+00:00
-- url     : https://prove2.me/theorems/5e1a00fd-98f3-41d5-8e99-eb5e39cb702a
-- title:
--   Dvr Model: prime res
-- statement:
--   The Dvr Model construction uses the prime res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L117-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L117-L128

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

theorem GlobalTheory.DvrModel.prime_res (hϖ : Irreducible ϖ) [Flat f] [IsIntegral Hs]
    (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V)))) {U : H.Opens}
    (hU : IsAffineOpen U) {x : H} (hx : x ∈ U) (hfx : f x = closedPoint V) :
    Prime (H.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op cst[f, V, ϖ]) := by sorry
