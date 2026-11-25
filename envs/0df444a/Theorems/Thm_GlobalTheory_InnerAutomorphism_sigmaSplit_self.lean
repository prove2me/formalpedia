-- Prove2me | Theorems.Thm_GlobalTheory_InnerAutomorphism_sigmaSplit_self
-- name    : GlobalTheory.InnerAutomorphism.sigmaSplit_self
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:10:27.001963+00:00
-- url     : https://prove2.me/theorems/12aa4da4-ba4d-44ce-9912-523ab964781d
-- title:
--   Inner Automorphism: sigma Split self
-- statement:
--   The Inner Automorphism construction uses the sigma Split self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SigmaSplitSymmInl.lean#L79-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SigmaSplitSymmInl.lean#L79-L80

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
variable {ι : Type*} [DecidableEq ι] (F : ι → Type*)

theorem GlobalTheory.InnerAutomorphism.sigmaSplit_self (j : ι) (x : F j) : sigmaSplit F j ⟨j, x⟩ = Sum.inl x := by sorry
