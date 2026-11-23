-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLeft_sq_norm_cos
-- name    : GlobalTheory.CompanionTheory.DigammaLeft.sq_norm_cos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:18.557805+00:00
-- url     : https://prove2.me/theorems/90edc85c-8238-4337-bc69-2063c580959d
-- title:
--   Digamma Left: sq norm cos
-- statement:
--   The Digamma Left construction uses the sq norm cos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundLeftRegion.lean#L69-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundLeftRegion.lean#L69-L77

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

theorem GlobalTheory.CompanionTheory.DigammaLeft.sq_norm_cos (z : ℂ) :
    ‖Complex.cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by sorry
