-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLeft_norm_cos_le_of_im
-- name    : GlobalTheory.CompanionTheory.DigammaLeft.norm_cos_le_of_im
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:35:07.004275+00:00
-- url     : https://prove2.me/theorems/291182c8-acac-4f24-b332-cc9221138423
-- title:
--   Digamma Left: norm cos le of im
-- statement:
--   The Digamma Left construction uses the norm cos le of im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundLeftRegion.lean#L79-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundLeftRegion.lean#L79-L89

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

theorem GlobalTheory.CompanionTheory.DigammaLeft.norm_cos_le_of_im (z : ℂ) (h : 1 ≤ |z.im|) : ‖Complex.cos z‖ ≤ 2 * ‖Complex.sin z‖ := by sorry
