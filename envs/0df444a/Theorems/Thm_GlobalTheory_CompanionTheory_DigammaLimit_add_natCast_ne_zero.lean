-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_add_natCast_ne_zero
-- name    : GlobalTheory.CompanionTheory.DigammaLimit.add_natCast_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:01.651683+00:00
-- url     : https://prove2.me/theorems/65104b65-718d-49a7-bc37-0b6a4263b06e
-- title:
--   Digamma Limit: add nat Cast ne zero
-- statement:
--   The Digamma Limit construction uses the add nat Cast ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean#L43-L48

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Metric Set
open scoped Nat Real
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaLimit

theorem GlobalTheory.CompanionTheory.DigammaLimit.add_natCast_ne_zero {z : ℂ} (hz : 0 < z.re) (j : ℕ) : z + (j : ℂ) ≠ 0 := by sorry
