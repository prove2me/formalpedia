-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_cechTripleRestrictComposite_comp_pairRestrict
-- name    : GlobalTheory.CechDR.cechTripleRestrictComposite_comp_pairRestrict
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:51:20.827162+00:00
-- url     : https://prove2.me/theorems/5b9a9e6f-4190-48fa-b0a2-9b08a6f3c7c7
-- title:
--   Cech DR: cech Triple Restrict Composite comp pair Restrict
-- statement:
--   The Cech DR construction uses the cech Triple Restrict Composite comp pair Restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafCohomologyPullbackCompCupId.lean#L45-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafCohomologyPullbackCompCupId.lean#L45-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupId
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CechDR
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {ψ : X'' ⟶ X'} {φ : X' ⟶ X}
variable (ψ φ)

theorem GlobalTheory.CechDR.cechTripleRestrictComposite_comp_pairRestrict (s'' : X'' ⟶ Sp R'') :
    (∀ c : HO1 s'', (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 c) =
      (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))).pull1 c) ∧
    (∀ c : HO2 s'', (cechTripleRestrictComposite ψ φ s'').pull2 ((pairRes (ψ ≫ φ) s'').pull2 c) =
      (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))).pull2 c) ∧
    (∀ c : GlobForm s'', pullGlob1 (cechTripleRestrictComposite ψ φ s'') (pullGlob1 (pairRes (ψ ≫ φ) s'') c) =
      pullGlob1 (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))) c) := by sorry
