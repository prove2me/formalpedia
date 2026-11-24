-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_wronskian_eq_zero_of_moderate
-- name    : GroundTheory.Automorphic.ArchWhittaker.wronskian_eq_zero_of_moderate
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:28:54.28708+00:00
-- url     : https://prove2.me/theorems/be58e3e6-60df-42cc-9f0f-5b9b2b5d3f3c
-- title:
--   Arch Whittaker: wronskian eq zero of moderate
-- statement:
--   The Arch Whittaker construction uses the wronskian eq zero of moderate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/WronskianEqZeroOfModerate.lean#L334-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/WronskianEqZeroOfModerate.lean#L334-L350

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

theorem GroundTheory.Automorphic.ArchWhittaker.wronskian_eq_zero_of_moderate {q f f' g g' : ℝ → ℂ} {c M Y₀ : ℝ} (hY₀ : 0 < Y₀)
    (hc : 0 < c) (hqre : ∀ y ≥ Y₀, c ^ 2 ≤ (q y).re) (hqM : ∀ y ≥ Y₀, ‖q y‖ ≤ M)
    (hf : ∀ y > 0, HasDerivAt f (f' y) y) (hf' : ∀ y > 0, HasDerivAt f' (q y * f y) y)
    (hg : ∀ y > 0, HasDerivAt g (g' y) y) (hg' : ∀ y > 0, HasDerivAt g' (q y * g y) y)
    (hfgr : ∃ (C : ℝ) (N : ℕ), ∀ y ≥ Y₀, ‖f y‖ ≤ C * y ^ N)
    (hggr : ∃ (C : ℝ) (N : ℕ), ∀ y ≥ Y₀, ‖g y‖ ≤ C * y ^ N) :
    f 1 * g' 1 - f' 1 * g 1 = 0 := by sorry
