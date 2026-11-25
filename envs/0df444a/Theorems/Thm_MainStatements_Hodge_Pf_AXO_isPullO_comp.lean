-- Prove2me | Theorems.Thm_MainStatements_Hodge_Pf_AXO_isPullO_comp
-- name    : MainStatements.Hodge.Pf.AXO.isPullO_comp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:59:59.936982+00:00
-- url     : https://prove2.me/theorems/1ac125fa-78c8-47e9-b098-72f5a2b4aab0
-- title:
--   AXO: is Pull O comp
-- statement:
--   The AXO construction uses the is Pull O comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianPullbackLattices/CompositeRestrictionPullInjective.lean#L44-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianPullbackLattices/CompositeRestrictionPullInjective.lean#L44-L69

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianPullbackLattices_CompositeRestrictionPullInjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open MainStatements MainStatements.Hodge MainStatements.Hodge.Pf MainStatements.Hodge.Pf.AXO
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}

theorem MainStatements.Hodge.Pf.AXO.isPullO_comp {ρ : R →+* R''} (hρ : τ.comp σ = ρ) (h : φ ≫ s = s' ≫ spMap σ)
    (h' : ψ ≫ s' = s'' ≫ spMap τ) (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap ρ) (a : HO1 s) (a' : HO1 s')
    (a'' : HO1 s'') (p : IsPullO h a a') (p' : IsPullO h' a' a'') : IsPullO h'' a a'' := by sorry
