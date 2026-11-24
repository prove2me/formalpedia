-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaBound_harmonic_cast
-- name    : GlobalTheory.CompanionTheory.DigammaBound.harmonic_cast
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:35:06.312371+00:00
-- url     : https://prove2.me/theorems/275f8ac8-e2b0-4bed-bc3b-45290ac56306
-- title:
--   Digamma Bound: harmonic cast
-- statement:
--   The Digamma Bound construction uses the harmonic cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundRightHalfPlane.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundRightHalfPlane.lean#L84-L85

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaBound
open Finset

theorem GlobalTheory.CompanionTheory.DigammaBound.harmonic_cast (n : ℕ) : ((harmonic n : ℚ) : ℝ) = ∑ i ∈ range n, ((i : ℝ) + 1)⁻¹ := by sorry
