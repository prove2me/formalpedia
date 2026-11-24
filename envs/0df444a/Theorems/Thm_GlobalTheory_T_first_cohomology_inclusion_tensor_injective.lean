-- Prove2me | Theorems.Thm_GlobalTheory_T_first_cohomology_inclusion_tensor_injective
-- name    : GlobalTheory.T.first_cohomology_inclusion_tensor_injective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:41:33.363277+00:00
-- url     : https://prove2.me/theorems/7e625d28-a46d-460d-b9c0-b1e787a4097f
-- title:
--   T: first cohomology inclusion tensor injective
-- statement:
--   The T construction uses the first cohomology inclusion tensor injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FirstCohomologyInclusionTensorInjectiveStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FirstCohomologyInclusionTensorInjectiveStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyInclusionTensorInjective
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyInclusionTensorInjectiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.first_cohomology_inclusion_tensor_injective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), H1CommutesBaseChange F → ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective ((iotaQ F).lTensor M) := by sorry
