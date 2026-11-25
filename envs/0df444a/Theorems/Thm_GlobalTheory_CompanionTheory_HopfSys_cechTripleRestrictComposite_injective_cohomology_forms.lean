-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_cechTripleRestrictComposite_injective_cohomology_forms
-- name    : GlobalTheory.CompanionTheory.HopfSys.cechTripleRestrictComposite_injective_cohomology_forms
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:36:13.388851+00:00
-- url     : https://prove2.me/theorems/f5961386-2810-4b07-90d0-8e8ee3491686
-- title:
--   Hopf Sys: cech Triple Restrict Composite injective cohomology forms
-- statement:
--   The Hopf Sys construction uses the cech Triple Restrict Composite injective cohomology forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L116-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L116-L127

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HopfSys
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}

theorem GlobalTheory.CompanionTheory.HopfSys.cechTripleRestrictComposite_injective_cohomology_forms (ψ : X'' ⟶ X') (φ : X' ⟶ X) (s'' : X'' ⟶ Sp R'') :
    Function.Injective (cechTripleRestrictComposite ψ φ s'').pull1 := by sorry
