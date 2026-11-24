-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SpectralAlgClosure_norm_eq_spectralNorm
-- name    : GroundTheory.PAdicHodge.SpectralAlgClosure.norm_eq_spectralNorm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:51.015885+00:00
-- url     : https://prove2.me/theorems/a904b81e-731b-4530-95e1-f77f7d770293
-- title:
--   Spectral Alg Closure: norm eq spectral Norm
-- statement:
--   The Spectral Alg Closure construction uses the norm eq spectral Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CompletedAlgClosure.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CompletedAlgClosure.lean#L30-L32

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CompletedAlgClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable (K : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
open GroundTheory.PAdicHodge.SpectralAlgClosure

theorem GroundTheory.PAdicHodge.SpectralAlgClosure.norm_eq_spectralNorm (x : SpectralAlgClosure K) :
    ‖x‖ = spectralNorm K (SpectralAlgClosure K) x := by sorry
