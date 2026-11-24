-- Prove2me | Theorems.Thm_GlobalTheory_CubeFrame_cube_eq_on_ball
-- name    : GlobalTheory.CubeFrame.cube_eq_on_ball
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:28:13.470804+00:00
-- url     : https://prove2.me/theorems/7681d6ba-013c-4024-91d0-431b4a6f2bc9
-- title:
--   Cube Frame: cube eq on ball
-- statement:
--   The Cube Frame construction uses the cube eq on ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsGlobalFrameOfLocal.lean#L53-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsGlobalFrameOfLocal.lean#L53-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsGlobalFrameOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.CubeFrame
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {ι : Type} {W : ι → Set E} {c : ι → ι → E → ℂ}
  {T : (Finset (Fin 3) → ι) → (Fin 3 → E) → ℂ}

theorem GlobalTheory.CubeFrame.cube_eq_on_ball (hW : ∀ i, IsOpen (W i)) (hcov : ∀ z, ∃ i, z ∈ W i)
    (hc0 : ∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0)
    (hT : ∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))})
    (hTc : ∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) →
      T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) *
        T j' x)
    {r : ℝ} {fr : ι → E → ℂ} {κ : ℂ} (hr : 0 < r)
    (hfd : ∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r))
    (hf0 : ∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0)
    (hfc : ∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)
    (hev : ∀ᶠ x in 𝓝 (0 : Fin 3 → E), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) :
    ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ Metric.ball (0 : E) r) →
      T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card)) := by sorry
