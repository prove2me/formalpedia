-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_WordRAM_wordLengthProgram_correct
-- name    : ITPIRPreproc.MatchVec.WordRAM.wordLengthProgram_correct
-- status  : Proved
-- author  : @Jesko
-- created : 2026-11-13T18:26:10.814544+00:00
-- url     : https://prove2.me/theorems/e9b186d8-aa72-4918-a3f2-667423d91c6a
-- title:
--   Polynomial-work RAM computation of the exact matching-vector word length
-- statement:
--   Let $h$ be a nonnegative integer and let $\ell(h)=\min\{t\ge0:2^h\le t^t\}$, with $0^0=1$. The explicit 35-instruction word-RAM program is deterministic and streaming. Given the self-delimiting encoding of $h$ followed by any suffix, it halts with $h$, $2^h$, and $\ell(h)$ in registers 0, 1, and 2, respectively. It consumes exactly the encoding of $h$, leaves the suffix unread, and writes no output. For every coin tape, it satisfies
--   $$\text{steps}\le50(h+2)^2,\qquad \text{charged work}\le200(h+2)^4,\qquad \text{working bits}\le8((h+2)^2+1).$$
--   This verifies computation of the exact least word-length parameter used by the polynomial matching-vector family, from the standard initial machine state. The work and storage bounds refer to the mission's original word-RAM model. It is one component of the uniform indexed construction; coefficients, coordinate enumeration, and vector output are not asserted by this theorem.
-- source:
--   Derived implementation lemma for Definitions.Def_ITPIRPreproc_MatchVec_RAMParameters and the least-word-length specification in Definitions.Def_ITPIRPreproc_MatchVec_PolynomialParameters, corresponding to Appendix A of Dujmovic-Lai-Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572. The program and explicit runtime constants are supplied by this formalization.

import Definitions.Def_ITPIRPreproc_MatchVec_RAMParameters
import Definitions.Def_ITPIRPreproc_MatchVec_PolynomialParameters
import Mathlib.Tactic
open ITPIRPreproc.MatchVec ITPIRPreproc.MatchVec.WordRAM ITPIRPreproc.MatchVec.PolynomialConstruction

theorem ITPIRPreproc.MatchVec.WordRAM.wordLengthProgram_correct :
    Deterministic wordLengthProgram ∧ Streaming wordLengthProgram ∧
    ∀ (h : ℕ) (tail : List Bool) (ω : ℕ → Bool),
    Halts wordLengthProgram (encNat h++tail) ω ∧
    (finalState wordLengthProgram (encNat h++tail) ω).regs 0=h ∧
    (finalState wordLengthProgram (encNat h++tail) ω).regs 1=2^h ∧
    (finalState wordLengthProgram (encNat h++tail) ω).regs 2=wordLength h ∧
    (finalState wordLengthProgram (encNat h++tail) ω).inPos=(encNat h).length ∧
    output wordLengthProgram (encNat h++tail) ω=[] ∧
    haltStep wordLengthProgram (encNat h++tail) ω≤50*(h+2)^2 ∧
    cost wordLengthProgram (encNat h++tail) ω≤200*(h+2)^4 ∧
    workingBits wordLengthProgram (encNat h++tail) ω≤8*((h+2)^2+1) := by sorry
