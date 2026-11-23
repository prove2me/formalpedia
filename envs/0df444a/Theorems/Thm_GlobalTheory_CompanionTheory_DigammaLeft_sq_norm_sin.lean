-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLeft_sq_norm_sin
-- name    : GlobalTheory.CompanionTheory.DigammaLeft.sq_norm_sin
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:34.092952+00:00
-- url     : https://prove2.me/theorems/4421a92d-0061-4835-938f-7d625e4de255
-- title:
--   Digamma Left: sq norm sin
-- statement:
--   The Digamma Left construction uses the sq norm sin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundLeftRegion.lean#L59-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaLogBoundLeftRegion.lean#L59-L67

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

theorem GlobalTheory.CompanionTheory.DigammaLeft.sq_norm_sin (z : ℂ) :
    ‖Complex.sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by sorry
