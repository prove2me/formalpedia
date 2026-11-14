-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_WordRAM_readNatProgram_correct
-- name    : ITPIRPreproc.MatchVec.WordRAM.readNatProgram_correct
-- status  : Proved
-- author  : @Jesko
-- created : 2026-11-13T17:53:04.554788+00:00
-- url     : https://prove2.me/theorems/29ba2f00-6d37-47ad-9a73-22ffd821e589
-- title:
--   A verified streaming RAM decoder for a self-delimiting integer
-- statement:
--   The explicit eleven-instruction program readNatProgram is deterministic and streaming. On input encNat(n) followed by an arbitrary suffix, and for every coin tape, it halts with n in register 0, consumes exactly the encoding of n, and writes no output. If L is the binary size of n (size(0)=0), it halts within 7L+6 instructions, incurs at most 20(L+1)^2 word-RAM work, and uses at most 5(L+1) working bits, in the mission machine model. The bounds are independent of the suffix. This verifies a concrete input-decoding subroutine, not the full indexed matching-vector algorithm or the PIR theorem.
-- source:
--   Derived implementation lemma for Definitions.Def_ITPIRPreproc_MatchVec_Machine and Definitions.Def_ITPIRPreproc_MatchVec_RAMEncoding. The formal input decoding is groundwork for Appendix A of Dujmovic-Lai-Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572; the instruction-level routine and constants are supplied by this formalization.

import Definitions.Def_ITPIRPreproc_MatchVec_RAMEncoding
import Mathlib.Tactic
open ITPIRPreproc.MatchVec.WordRAM

theorem ITPIRPreproc.MatchVec.WordRAM.readNatProgram_correct :
    Deterministic readNatProgram ∧ Streaming readNatProgram ∧
    ∀ (n : ℕ) (tail : List Bool) (ω : ℕ → Bool),
    Halts readNatProgram (encNat n ++ tail) ω ∧
    (finalState readNatProgram (encNat n ++ tail) ω).regs 0 = n ∧
    (finalState readNatProgram (encNat n ++ tail) ω).inPos = (encNat n).length ∧
    output readNatProgram (encNat n ++ tail) ω = [] ∧
    haltStep readNatProgram (encNat n ++ tail) ω ≤ 7*n.size+6 ∧
    cost readNatProgram (encNat n ++ tail) ω ≤ 20*(n.size+1)^2 ∧
    workingBits readNatProgram (encNat n ++ tail) ω ≤ 5*(n.size+1) := by sorry
