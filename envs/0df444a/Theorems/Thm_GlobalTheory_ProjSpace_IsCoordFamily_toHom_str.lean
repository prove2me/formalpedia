-- Prove2me | Theorems.Thm_GlobalTheory_ProjSpace_IsCoordFamily_toHom_str
-- name    : GlobalTheory.ProjSpace.IsCoordFamily.toHom_str
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:28:03.608121+00:00
-- url     : https://prove2.me/theorems/0ee9d52c-2c97-4997-8fc5-3f45170026e8
-- title:
--   Is Coord Family: to Hom str
-- statement:
--   The Is Coord Family construction uses the to Hom str property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean#L284-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean#L284-L287

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

theorem GlobalTheory.ProjSpace.IsCoordFamily.toHom_str (f : Y ⟶ Sp R) : H.toHom f ≫ PSpace.str R N = f := by sorry
