-- Prove2me | Theorems.Thm_GlobalTheory_apply_perpVector
-- name    : GlobalTheory.apply_perpVector
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:05:35.668361+00:00
-- url     : https://prove2.me/theorems/319d1e45-9958-4899-899e-a419aad74a84
-- title:
--   Global Theory: apply perp Vector
-- statement:
--   The Global Theory construction uses the apply perp Vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L22-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L22-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.apply_perpVector (ε : ι → Module.Dual R M) (e' : ι → M) (g : M) (c : ι) :
    ε c (perpVector ε e' g) = 0 := by sorry
