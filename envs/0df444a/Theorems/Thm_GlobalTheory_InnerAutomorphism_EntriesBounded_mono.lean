-- Prove2me | Theorems.Thm_GlobalTheory_InnerAutomorphism_EntriesBounded_mono
-- name    : GlobalTheory.InnerAutomorphism.EntriesBounded.mono
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:10:30.401805+00:00
-- url     : https://prove2.me/theorems/05fab72d-ca2d-4809-b876-32e57dd52dee
-- title:
--   Entries Bounded: mono
-- statement:
--   The Entries Bounded construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SigmaSplitSymmInl.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SigmaSplitSymmInl.lean#L30-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SigmaSplitSymmInl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InnerAutomorphism
variable {K n : Type*} [NormedField K]

theorem GlobalTheory.InnerAutomorphism.EntriesBounded.mono {M : Matrix n n K} {c d : ℝ} (h : EntriesBounded M c)
    (hcd : c ≤ d) : EntriesBounded M d := by sorry
