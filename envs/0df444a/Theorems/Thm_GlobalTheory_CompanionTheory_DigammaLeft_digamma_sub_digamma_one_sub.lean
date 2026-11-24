-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLeft_digamma_sub_digamma_one_sub
-- name    : GlobalTheory.CompanionTheory.DigammaLeft.digamma_sub_digamma_one_sub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:35:31.904835+00:00
-- url     : https://prove2.me/theorems/dd674d48-ae27-4e19-95f0-25cccdc3552e
-- title:
--   Digamma Left: digamma sub digamma one sub
-- statement:
--   The Digamma Left construction uses the digamma sub digamma one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundLeftRegion.lean#L6-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundLeftRegion.lean#L6-L57

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

theorem GlobalTheory.CompanionTheory.DigammaLeft.digamma_sub_digamma_one_sub (w : ℂ) (hw : ∀ n : ℤ, w ≠ n) :
    Complex.digamma w - Complex.digamma (1 - w) =
      -((Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)) := by sorry
