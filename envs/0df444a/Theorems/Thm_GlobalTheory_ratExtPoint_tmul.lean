-- Prove2me | Theorems.Thm_GlobalTheory_ratExtPoint_tmul
-- name    : GlobalTheory.ratExtPoint_tmul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:16:17.228714+00:00
-- url     : https://prove2.me/theorems/d5632491-d3b0-4909-9b77-e9fb420c220f
-- title:
--   Global Theory: rat Ext Point tmul
-- statement:
--   The Global Theory construction uses the rat Ext Point tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalMaxPrincipleWeightedFiniteTypeInt.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalMaxPrincipleWeightedFiniteTypeInt.lean#L23-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalMaximumPrincipleWeightFiniteMvPolynomialStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalMaxPrincipleWeightedFiniteTypeInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.ratExtPoint_tmul {B : Type} [CommRing B] (x : B →+* ℂ) (q : ℚ) (b : B) :
    ratExtPoint x (q ⊗ₜ[ℤ] b) = (q : ℂ) * x b := by sorry
