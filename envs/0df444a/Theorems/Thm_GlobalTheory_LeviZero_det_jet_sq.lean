-- Prove2me | Theorems.Thm_GlobalTheory_LeviZero_det_jet_sq
-- name    : GlobalTheory.LeviZero.det_jet_sq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:48:23.672518+00:00
-- url     : https://prove2.me/theorems/f55586a8-bfe1-599d-b6d2-4d94f291f15a
-- title:
--   Levi Zero: det jet sq
-- statement:
--   The Levi Zero construction uses the det jet sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeviFormWeightMetricOrthonormalDiagonal.lean#L187-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeviFormWeightMetricOrthonormalDiagonal.lean#L187-L225

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LeviZero
open Filter
open scoped ComplexConjugate
noncomputable section
variable {A : Type*} [CommRing A]

theorem GlobalTheory.LeviZero.det_jet_sq {m : ℕ} {s t : A} (hs : s * s = 0) (ht : t * t = 0) (ε : Fin m → A)
    (hε : ∀ a, ε a * ε a = 1) (Z Z' R : Matrix (Fin m) (Fin m) A)
    (hZ : ∀ a b, a ≤ b → Z a b = 0) (hZ' : ∀ a b, a ≤ b → Z' a b = 0) :
    (Matrix.diagonal ε + s • (Zᵀ * Matrix.diagonal ε) + t • (Matrix.diagonal ε * Z') +
      (s * t) • R).det =
      (∏ a, ε a) * (1 + (∑ b, ε b * (R b b - ∑ a, Z a b * ε a * Z' a b)) * (s * t)) := by sorry
