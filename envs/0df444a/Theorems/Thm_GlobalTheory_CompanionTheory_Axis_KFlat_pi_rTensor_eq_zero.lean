-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Axis_KFlat_pi_rTensor_eq_zero
-- name    : GlobalTheory.CompanionTheory.Axis.KFlat.pi_rTensor_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:15:54.729044+00:00
-- url     : https://prove2.me/theorems/1b79f0ff-1363-4747-8df2-35bc1343d7f7
-- title:
--   KFlat: pi r Tensor eq zero
-- statement:
--   The KFlat construction uses the pi r Tensor eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CocycleTensorCoboundaryClassZero.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CocycleTensorCoboundaryClassZero.lean#L28-L35

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleTensorCoboundaryClassZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis GlobalTheory.CompanionTheory.Axis.KFlat
variable {R : Type} [CommRing R] {J : Type} [Finite J] {M : J → Type} [∀ i, AddCommGroup (M i)]
  [∀ i, Module R (M i)] {N : Type} [AddCommGroup N] [Module R N]

theorem GlobalTheory.CompanionTheory.Axis.KFlat.pi_rTensor_eq_zero (w : (∀ i, M i) ⊗[R] N)
    (h : ∀ i, (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i).rTensor N w = 0) : w = 0 := by sorry
