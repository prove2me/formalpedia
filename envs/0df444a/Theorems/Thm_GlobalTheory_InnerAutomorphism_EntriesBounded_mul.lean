-- Prove2me | Theorems.Thm_GlobalTheory_InnerAutomorphism_EntriesBounded_mul
-- name    : GlobalTheory.InnerAutomorphism.EntriesBounded.mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:10:25.998609+00:00
-- url     : https://prove2.me/theorems/6ea3459d-ddca-4868-94fd-98e8ce3b3f17
-- title:
--   Entries Bounded: mul
-- statement:
--   The Entries Bounded construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SigmaSplitSymmInl.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SigmaSplitSymmInl.lean#L34-L44

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

theorem GlobalTheory.InnerAutomorphism.EntriesBounded.mul [IsUltrametricDist K] [Fintype n] {M N : Matrix n n K} {c d : ℝ}
    (hM : EntriesBounded M c) (hN : EntriesBounded N d) :
    EntriesBounded (M * N) (c * d) := by sorry
