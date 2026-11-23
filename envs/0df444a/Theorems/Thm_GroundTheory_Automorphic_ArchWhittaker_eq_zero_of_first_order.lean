-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_eq_zero_of_first_order
-- name    : GroundTheory.Automorphic.ArchWhittaker.eq_zero_of_first_order
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:29.476907+00:00
-- url     : https://prove2.me/theorems/a3242718-8fc1-42b0-9e5e-8b58aeb14055
-- title:
--   Arch Whittaker: eq zero of first order
-- statement:
--   The Arch Whittaker construction uses the eq zero of first order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/WronskianEqZeroOfModerate.lean#L352-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/WronskianEqZeroOfModerate.lean#L352-L427

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

theorem GroundTheory.Automorphic.ArchWhittaker.eq_zero_of_first_order {F : ℝ → ℂ} {m : ℤ} {b : ℝ} (hb : 0 < b)
    (hF : ∀ y > 0, HasDerivAt F ((((m : ℝ) / (2 * y) + b : ℝ) : ℂ) * F y) y)
    (hgr : ∃ (C : ℝ) (N : ℕ), ∀ y ≥ 1, ‖F y‖ ≤ C * y ^ N) : ∀ y > 0, F y = 0 := by sorry
