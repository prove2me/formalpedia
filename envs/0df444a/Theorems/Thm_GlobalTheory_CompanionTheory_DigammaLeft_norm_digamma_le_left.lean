-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLeft_norm_digamma_le_left
-- name    : GlobalTheory.CompanionTheory.DigammaLeft.norm_digamma_le_left
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:35:21.402734+00:00
-- url     : https://prove2.me/theorems/8db58878-f8fb-43fe-9f52-49bb4461780e
-- title:
--   Digamma Left: norm digamma le left
-- statement:
--   The Digamma Left construction uses the norm digamma le left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundLeftRegion.lean#L106-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundLeftRegion.lean#L106-L162

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundLeftRegion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaLeft

theorem GlobalTheory.CompanionTheory.DigammaLeft.norm_digamma_le_left :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w.re ≤ 1 / 4 →
      (1 / 2 ≤ |w.im| ∨ ∃ k : ℤ, w.re = (k : ℝ) / 2 + 1 / 4) →
      ‖Complex.digamma w‖ ≤ C * Real.log (‖w‖ + 2) := by sorry
