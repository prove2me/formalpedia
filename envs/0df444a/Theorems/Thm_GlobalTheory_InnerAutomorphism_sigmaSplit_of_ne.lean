-- Prove2me | Theorems.Thm_GlobalTheory_InnerAutomorphism_sigmaSplit_of_ne
-- name    : GlobalTheory.InnerAutomorphism.sigmaSplit_of_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:10:11.230115+00:00
-- url     : https://prove2.me/theorems/fe401910-d1ad-57ed-9d7d-00dfb694cc26
-- title:
--   Inner Automorphism: sigma Split of ne
-- statement:
--   The Inner Automorphism construction uses the sigma Split of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SigmaSplitSymmInl.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SigmaSplitSymmInl.lean#L82-L84

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

theorem GlobalTheory.InnerAutomorphism.sigmaSplit_of_ne {i j : ι} (h : i ≠ j) (x : F i) :
    sigmaSplit F j ⟨i, x⟩ = Sum.inr ⟨⟨i, h⟩, x⟩ := by sorry
