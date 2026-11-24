-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_evaluation_zero_tmul
-- name    : GlobalTheory.CompanionTheory.WedgeOf.evaluation_zero_tmul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:31:45.613914+00:00
-- url     : https://prove2.me/theorems/a618973a-19f2-4797-89c5-ab8f04162e87
-- title:
--   Wedge Of: evaluation zero tmul
-- statement:
--   The Wedge Of construction uses the evaluation zero tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FirstCohomologyInclusionTensorInjective.lean#L43-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FirstCohomologyInclusionTensorInjective.lean#L43-L43

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

theorem GlobalTheory.CompanionTheory.WedgeOf.evaluation_zero_tmul (n : M) (g : C0 F) (T : C) : ev0 F j (n ⊗ₜ g) T = j n ⊗ₜ g T := by sorry
