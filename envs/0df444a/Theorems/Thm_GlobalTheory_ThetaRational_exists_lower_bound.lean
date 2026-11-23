-- Prove2me | Theorems.Thm_GlobalTheory_ThetaRational_exists_lower_bound
-- name    : GlobalTheory.ThetaRational.exists_lower_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:03:50.078802+00:00
-- url     : https://prove2.me/theorems/d9be9ba4-59be-448b-89eb-df5478ae6d2f
-- title:
--   Theta Rational: exists lower bound
-- statement:
--   The Theta Rational construction uses the exists lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L72-L77

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {θ : V → W} {f : V → ℂ} {d : ℕ} {Λ K : Set V}
omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [NormedSpace ℂ V] [NormedSpace ℂ W]

theorem GlobalTheory.ThetaRational.exists_lower_bound (hK : IsCompact K) (hθ : Continuous θ) (hN : ∀ z, θ z ≠ 0) :
    ∃ ε > 0, ∀ k ∈ K, ε ≤ ‖θ k‖ := by sorry
