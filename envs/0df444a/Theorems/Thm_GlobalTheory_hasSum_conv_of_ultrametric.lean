-- Prove2me | Theorems.Thm_GlobalTheory_hasSum_conv_of_ultrametric
-- name    : GlobalTheory.hasSum_conv_of_ultrametric
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:14.805803+00:00
-- url     : https://prove2.me/theorems/3d1e3e0a-7a68-4286-be8e-890a1f0c2513
-- title:
--   Global Theory: has Sum conv of ultrametric
-- statement:
--   The Global Theory construction uses the has Sum conv of ultrametric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HasSumGradedOfMulDegree.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HasSumGradedOfMulDegree.lean#L7-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HasSumGradedOfMulDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory

theorem GlobalTheory.hasSum_conv_of_ultrametric {C : Type} [NormedField C] [IsUltrametricDist C]
    {X : Type} [AddCommGroup X] {a a' a'' : X → C} {S S' : C}
    (h : HasSum a S) (h' : HasSum a' S')
    (hc : ∀ α, HasSum (fun χ => a χ * a' (α - χ)) (a'' α)) : HasSum a'' (S * S') := by sorry
