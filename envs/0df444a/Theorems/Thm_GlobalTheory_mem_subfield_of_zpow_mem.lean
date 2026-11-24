-- Prove2me | Theorems.Thm_GlobalTheory_mem_subfield_of_zpow_mem
-- name    : GlobalTheory.mem_subfield_of_zpow_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:11:01.850457+00:00
-- url     : https://prove2.me/theorems/10b4cd20-8b90-4621-ba76-431612c2994e
-- title:
--   Global Theory: mem subfield of zpow mem
-- statement:
--   The Global Theory construction uses the mem subfield of zpow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSubfieldOfBilinFormBasisMonomials.lean#L5-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSubfieldOfBilinFormBasisMonomials.lean#L5-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSubfieldOfBilinFormBasisMonomials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.mem_subfield_of_zpow_mem {K : Type} [Field K] (k₀ : Subfield K) [IsAlgClosed k₀]
    (u : Kˣ) (m : ℤ) (hm : m ≠ 0) (h : ((u ^ m : Kˣ) : K) ∈ k₀) : (u : K) ∈ k₀ := by sorry
