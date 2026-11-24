-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTate_mem_of_orth
-- name    : GlobalTheory.HeckeTate.mem_of_orth
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:05:39.852637+00:00
-- url     : https://prove2.me/theorems/ccaf0027-29fc-4345-a06f-999e1b626fe4
-- title:
--   Hecke Tate: mem of orth
-- statement:
--   The Hecke Tate construction uses the mem of orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUnimodDiv.lean#L44-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUnimodDiv.lean#L44-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.HeckeTate

theorem GlobalTheory.HeckeTate.mem_of_orth {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] (B : M →+ M →+ ℤ)
    (hB : Function.Bijective B) {m c : ℕ} (hm : m ≠ 0) (hg : m ^ Module.finrank ℤ M = c * c) (C : AddSubgroup M)
    (hC : (nsmulAddMonoidHom (α := M) m).range ≤ C)
    (hc : (nsmulAddMonoidHom (α := M) m).range.relIndex C = c)
    (hiso : ∀ x ∈ C, ∀ y ∈ C, (m : ℤ) ∣ B x y) (x : M) (hx : ∀ y ∈ C, (m : ℤ) ∣ B x y) : x ∈ C := by sorry
