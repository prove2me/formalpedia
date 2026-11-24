-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_tendsto_zero_of_moderate
-- name    : GroundTheory.Automorphic.ArchWhittaker.tendsto_zero_of_moderate
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:18.375358+00:00
-- url     : https://prove2.me/theorems/45f8bcdf-ce2c-4154-a3bb-81a6d7c24544
-- title:
--   Arch Whittaker: tendsto zero of moderate
-- statement:
--   The Arch Whittaker construction uses the tendsto zero of moderate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/WronskianEqZeroOfModerate.lean#L53-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/WronskianEqZeroOfModerate.lean#L53-L199

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_WronskianEqZeroOfModerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ArchWhittaker
open Filter Topology Set

theorem GroundTheory.Automorphic.ArchWhittaker.tendsto_zero_of_moderate {q f f' : ℝ → ℂ} {Y₀ c C : ℝ} {N : ℕ} (hc : 0 < c)
    (hq : ∀ y ≥ Y₀, c ^ 2 ≤ (q y).re)
    (hf : ∀ y ≥ Y₀, HasDerivAt f (f' y) y) (hf' : ∀ y ≥ Y₀, HasDerivAt f' (q y * f y) y)
    (hgr : ∀ y ≥ Y₀, ‖f y‖ ≤ C * y ^ N) : Tendsto f atTop (𝓝 0) := by sorry
