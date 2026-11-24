-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_spo_spo_xo
-- name    : GlobalTheory.CompanionTheory.AbForms.spo_spo_xo
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:22:36.700496+00:00
-- url     : https://prove2.me/theorems/23837df2-e8cd-457d-868c-6acf8b345dad
-- title:
--   Ab Forms: spo spo xo
-- statement:
--   The Ab Forms construction uses the spo spo xo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UOfIsBaseChange.lean#L124-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UOfIsBaseChange.lean#L124-L132

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AbForms
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R : Type} [CommRing R]
variable {A : Over (Sp R)} [GrpObj A] {B : Type} [CommRing B] [Algebra R B]
variable {M : Type} [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
  (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (algebraMap R B))
variable {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M']
  [IsCentralScalar B' M']

theorem GlobalTheory.CompanionTheory.AbForms.spo_spo_xo (x' : Sp B' ⟶ A.left) (hx' : x' ≫ A.hom = spMap (algebraMap R B'))
    (α : B →+* B') (hxx : x' = spMap α ≫ x)
    {T T' : Type} [CommRing T] [CommRing T'] {f : R →+* T} {f' : R →+* T'} (ψ : T →+* T')
    (hψ : ψ.comp f = f') (τ : B →+* T) (hτ : τ.comp (algebraMap R B) = f)
    (τ' : B' →+* T') (hτ' : τ'.comp (algebraMap R B') = f') (e : ψ.comp τ = τ'.comp α) :
    spo ψ hψ ≫ spo τ hτ ≫ xo x hx = spo τ' hτ' ≫ xo x' hx' := by sorry
