-- Prove2me | Theorems.Thm_GlobalTheory_T_cocycle_tensor_coboundary_class_zero
-- name    : GlobalTheory.T.cocycle_tensor_coboundary_class_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:27:45.713036+00:00
-- url     : https://prove2.me/theorems/7dc7aaac-358f-4d4c-aa2c-1ecd9f2a7d8b
-- title:
--   T: cocycle tensor coboundary class zero
-- statement:
--   The T construction uses the cocycle tensor coboundary class zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CocycleTensorCoboundaryClassZeroStatement.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CocycleTensorCoboundaryClassZeroStatement.lean#L12-L16

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleTensorCoboundaryClassZero
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleTensorCoboundaryClassZeroStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.cocycle_tensor_coboundary_class_zero : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C] (F : C ⥤ CommAlgCat.{0} R)
    (N : Type) [AddCommGroup N] [Module R N] [Module.Flat R N] (t : Z1 F ⊗[R] N) (g : ∀ T : C, F.obj T ⊗[R] N),
    (∀ (T T' : C) (φ : T ⟶ T'), (evZ F φ).rTensor N t = g T' - (mp F φ).toLinearMap.rTensor N (g T)) →
    (H1.mk F).rTensor N t = 0 := by sorry
