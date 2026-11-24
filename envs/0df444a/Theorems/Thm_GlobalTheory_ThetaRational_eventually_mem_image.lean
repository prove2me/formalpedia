-- Prove2me | Theorems.Thm_GlobalTheory_ThetaRational_eventually_mem_image
-- name    : GlobalTheory.ThetaRational.eventually_mem_image
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:05:59.506185+00:00
-- url     : https://prove2.me/theorems/b3578e3c-012b-411c-b1c7-faba7afc5920
-- title:
--   Theta Rational: eventually mem image
-- statement:
--   The Theta Rational construction uses the eventually mem image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L128-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L128-L166

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
omit [FiniteDimensional ℂ W]

theorem GlobalTheory.ThetaRational.eventually_mem_image (hK : IsCompact K) (hθ : Continuous θ) (hN : ∀ z, θ z ≠ 0)
    (hP : ∀ z, ∃ k ∈ K, z - k ∈ Λ)
    (hL : ∀ l ∈ Λ, ∃ κ : V → ℂ, Continuous κ ∧ ∀ z, κ z ≠ 0 ∧ θ (z + l) = κ z • θ z ∧
      f (z + l) = κ z ^ d * f z)
    (hS : ∀ (z z' : V) (γ : ℂ), θ z = γ • θ z' → z - z' ∈ Λ)
    {e : ℂ × V} (he : e.1 • θ e.2 ≠ 0) {U : Set (ℂ × V)} (hU : U ∈ 𝓝 e) :
    ∀ᶠ y in 𝓝 (e.1 • θ e.2), ∀ x : ℂ × V, x.1 • θ x.2 = y → ∃ x' ∈ U, x'.1 • θ x'.2 = y := by sorry
