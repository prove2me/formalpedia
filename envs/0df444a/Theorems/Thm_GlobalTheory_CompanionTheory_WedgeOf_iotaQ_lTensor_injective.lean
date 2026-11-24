-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_iotaQ_lTensor_injective
-- name    : GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:31:46.012603+00:00
-- url     : https://prove2.me/theorems/c0721ad8-a706-47a8-a93a-50e4b1a4c886
-- title:
--   Wedge Of: iota Q l Tensor injective
-- statement:
--   The Wedge Of construction uses the iota Q l Tensor injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FirstCohomologyInclusionTensorInjective.lean#L110-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FirstCohomologyInclusionTensorInjective.lean#L110-L116

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

theorem GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (h : H1CommutesBaseChange F) (M : Type) [AddCommGroup M] [Module R M] :
    Function.Injective ((iotaQ F).lTensor M) := by sorry
