-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_tendsto_deriv_zero
-- name    : GroundTheory.Automorphic.ArchWhittaker.tendsto_deriv_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:31.191677+00:00
-- url     : https://prove2.me/theorems/7e76cd8b-f313-4aa6-8c18-fc421fc6aaef
-- title:
--   Arch Whittaker: tendsto deriv zero
-- statement:
--   The Arch Whittaker construction uses the tendsto deriv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/WronskianEqZeroOfModerate.lean#L207-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/WronskianEqZeroOfModerate.lean#L207-L252

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

theorem GroundTheory.Automorphic.ArchWhittaker.tendsto_deriv_zero {q f f' : ℝ → ℂ} {Y₀ M : ℝ} (hqM : ∀ y ≥ Y₀, ‖q y‖ ≤ M)
    (hf : ∀ y ≥ Y₀, HasDerivAt f (f' y) y) (hf' : ∀ y ≥ Y₀, HasDerivAt f' (q y * f y) y)
    (hlim : Tendsto f atTop (𝓝 0)) : Tendsto f' atTop (𝓝 0) := by sorry
