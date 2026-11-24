-- Prove2me | Theorems.Thm_GlobalTheory_ClosedResidueExt_Unram_irreducible
-- name    : GlobalTheory.ClosedResidueExt.Unram.irreducible
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:13:17.744919+00:00
-- url     : https://prove2.me/theorems/9d3e216a-2f0a-46cc-a7bf-ca131b3a5556
-- title:
--   Unram: irreducible
-- statement:
--   The Unram construction uses the irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIntegralExtIsAlgClosedResidueField.lean#L27-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIntegralExtIsAlgClosedResidueField.lean#L27-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIntegralExtIsAlgClosedResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedResidueExt
open Polynomial IsLocalRing
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]

theorem GlobalTheory.ClosedResidueExt.Unram.irreducible {π : W} {R : Subalgebra W Ω} (h : Unram π R)
    (h0 : algebraMap W Ω π ≠ 0) : Irreducible (algebraMap W R π) := by sorry
