-- Prove2me | Theorems.Thm_GlobalTheory_finrank_int_eq_of_span_smul
-- name    : GlobalTheory.finrank_int_eq_of_span_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:49:34.722144+00:00
-- url     : https://prove2.me/theorems/f9c58ef3-88e9-4b56-bf1f-5d3c43689df4
-- title:
--   Global Theory: finrank int eq of span smul
-- statement:
--   The Global Theory construction uses the finrank int eq of span smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankEqRankMulDegree.lean#L18-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankEqRankMulDegree.lean#L18-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankEqRankMulDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory

theorem GlobalTheory.finrank_int_eq_of_span_smul (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M]
    [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M] (r : ℕ) (x : Fin r → M)
    (hx : LinearIndependent (𝓞 F) x) (c : 𝓞 F) (hc : c ≠ 0)
    (hspan : ∀ m : M, c • m ∈ Submodule.span (𝓞 F) (Set.range x)) :
    Module.finrank ℤ M = r * Module.finrank ℚ F := by sorry
