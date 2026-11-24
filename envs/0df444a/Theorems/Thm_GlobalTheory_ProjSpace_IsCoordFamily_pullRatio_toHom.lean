-- Prove2me | Theorems.Thm_GlobalTheory_ProjSpace_IsCoordFamily_pullRatio_toHom
-- name    : GlobalTheory.ProjSpace.IsCoordFamily.pullRatio_toHom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:49.276308+00:00
-- url     : https://prove2.me/theorems/e0faabe2-55cd-4000-87d1-d1f25ada2dd9
-- title:
--   Is Coord Family: pull Ratio to Hom
-- statement:
--   The Is Coord Family construction uses the pull Ratio to Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean#L296-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean#L296-L302

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG)
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace
variable {R : Type} [CommRing R] {N : ℕ} {Y Z : Scheme.{0}}
open GlobalTheory.ProjSpace.IsCoordFamily
variable {U : Fin (N + 1) → Y.Opens} {r : ∀ i, Fin (N + 1) → Γ(Y, U i)} (H : IsCoordFamily U r)
include H

theorem GlobalTheory.ProjSpace.IsCoordFamily.pullRatio_toHom (f : Y ⟶ Sp R) (i j : Fin (N + 1)) :
    pullRatio (H.toHom f) (U i) i (H.le_toHom_preimage f i) j = r i j := by sorry
