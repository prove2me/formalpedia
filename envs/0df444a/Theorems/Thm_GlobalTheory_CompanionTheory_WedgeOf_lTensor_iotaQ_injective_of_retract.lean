-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_lTensor_iotaQ_injective_of_retract
-- name    : GlobalTheory.CompanionTheory.WedgeOf.lTensor_iotaQ_injective_of_retract
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:31:43.618805+00:00
-- url     : https://prove2.me/theorems/68a0eadc-3d25-49f2-bbbc-6765a9031f20
-- title:
--   Wedge Of: l Tensor iota Q injective of retract
-- statement:
--   The Wedge Of construction uses the l Tensor iota Q injective of retract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FirstCohomologyInclusionTensorInjective.lean#L83-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FirstCohomologyInclusionTensorInjective.lean#L83-L106

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyInclusionTensorInjective
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
  (R' : Type) [CommRing R'] [Algebra R R']
variable {R'} {M : Type} [AddCommGroup M] [Module R M] (j : M →ₗ[R] R')

theorem GlobalTheory.CompanionTheory.WedgeOf.lTensor_iotaQ_injective_of_retract (h : H1CommutesBaseChange F) (p : R' →ₗ[R] M) (hp : p ∘ₗ j = LinearMap.id) :
    Function.Injective ((iotaQ F).lTensor M) := by sorry
