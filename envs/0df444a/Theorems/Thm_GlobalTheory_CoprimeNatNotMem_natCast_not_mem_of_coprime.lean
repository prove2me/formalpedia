-- Prove2me | Theorems.Thm_GlobalTheory_CoprimeNatNotMem_natCast_not_mem_of_coprime
-- name    : GlobalTheory.CoprimeNatNotMem.natCast_not_mem_of_coprime
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:02:48.773798+00:00
-- url     : https://prove2.me/theorems/e49e4d4b-b31b-425e-8418-a849e262a3e5
-- title:
--   Coprime Nat Not Mem: nat Cast not mem of coprime
-- statement:
--   The Coprime Nat Not Mem construction uses the nat Cast not mem of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCastNotMemOfCoprime.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCastNotMemOfCoprime.lean#L7-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCastNotMemOfCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.CoprimeNatNotMem

theorem GlobalTheory.CoprimeNatNotMem.natCast_not_mem_of_coprime {Rg : Type u_1} [CommRing Rg] {P : Ideal Rg} (hP : P ≠ ⊤)
    {p n : ℕ} (h : Nat.Coprime p n) (hp : (p : Rg) ∈ P) : (n : Rg) ∉ P := by sorry
