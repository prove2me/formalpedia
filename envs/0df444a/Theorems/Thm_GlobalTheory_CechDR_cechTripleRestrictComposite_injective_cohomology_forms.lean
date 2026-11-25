-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_cechTripleRestrictComposite_injective_cohomology_forms
-- name    : GlobalTheory.CechDR.cechTripleRestrictComposite_injective_cohomology_forms
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:01:09.514233+00:00
-- url     : https://prove2.me/theorems/7fb8726a-5ddc-5273-a64c-7bc674e0cc69
-- title:
--   Cech DR: cech Triple Restrict Composite injective cohomology forms
-- statement:
--   The Cech DR construction uses the cech Triple Restrict Composite injective cohomology forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafCohomologyPullbackCompCupId.lean#L62-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafCohomologyPullbackCompCupId.lean#L62-L89

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

theorem GlobalTheory.CechDR.cechTripleRestrictComposite_injective_cohomology_forms (s'' : X'' ⟶ Sp R'') :
    Function.Injective (cechTripleRestrictComposite ψ φ s'').pull1 ∧ Function.Injective (cechTripleRestrictComposite ψ φ s'').pull2 ∧
      Function.Injective (pullGlob1 (cechTripleRestrictComposite ψ φ s'')) := by sorry
