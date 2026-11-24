-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_exists_cocycle
-- name    : GlobalTheory.CompanionTheory.WedgeOf.exists_cocycle
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:31:51.541817+00:00
-- url     : https://prove2.me/theorems/ec1388d7-bb1b-43b8-a8c1-00f518d74ae7
-- title:
--   Wedge Of: exists cocycle
-- statement:
--   The Wedge Of construction uses the exists cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FirstCohomologyInclusionTensorInjective.lean#L62-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FirstCohomologyInclusionTensorInjective.lean#L62-L81

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

theorem GlobalTheory.CompanionTheory.WedgeOf.exists_cocycle (e : R' ⊗[R] H1 F ≃ₗ[R'] H1 (bcF F R'))
    (he : ∀ c, e (1 ⊗ₜ c) = (bcM F R').coef.pull1 c) (t : M ⊗[R] Z1 F) :
    ∃ z : Z1 (bcF F R'), z.1 = ev1 F j ((Z1 F).subtype.lTensor M t) ∧
      H1.mk (bcF F R') z = e (j.rTensor (H1 F) ((H1.mk F).lTensor M t)) := by sorry
