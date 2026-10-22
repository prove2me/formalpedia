-- Prove2me | Theorems.Thm_OptimalQueuingComplexity_Restless_circularTapeHalting_pspaceComplete
-- name    : OptimalQueuingComplexity.Restless.circularTapeHalting_pspaceComplete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T12:23:21.399983+00:00
-- url     : https://prove2.me/theorems/0d7e66d7-0ecf-48d6-bd29-c14f150a0dac
-- title:
--   Theorem 4 (proof, claim) — halting of the circular-tape process is PSPACE-complete
-- statement:
--   Consider the circular-tape process: squares $1,\dots,n$ with values in $\{1,\dots,A\}$, a rule $F$ with $F(1,1)=1$, and a head that at time $t$ replaces the value of the square $i \equiv t \pmod n$ by $F(v_{i-1 \bmod n}, v_i)$. The process halts if at some time every square holds the value $1$. Let CIRCULAR-TAPE HALTING be the problem of deciding, given an initial configuration and a rule $F$, whether the process halts. Then
--   $$\text{CIRCULAR-TAPE HALTING is PSPACE-complete,}$$
--   that is, it is decidable in polynomial space, and every language decidable in polynomial space reduces to it by a polynomial-time many-one reduction.
--
--   In the paper this claim is the first step of the proof of Theorem 4: the problem is the source of the reduction to RESTLESS BANDITS. Only its hardness half is needed there.
--
--   **Formalization Note.** Instances are encoded as in the definition of the problem (the dimensions $n$ and $A$ in binary, the $A^2$-entry table of $F$ and the $n$ initial values), and space is counted in stack symbols of a multi-stack Turing machine.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), p. 303, proof of Theorem 4 (claim)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Definitions.Def_OptimalQueuingComplexity_Restless_circularTapeHalting

namespace OptimalQueuingComplexity.Restless

/-- Papadimitriou & Tsitsiklis 1999, p. 303, proof of Theorem 4 (claim): deciding, given an
initial configuration of the circular tape and a rule `F`, whether the process eventually halts
is PSPACE-complete. -/
theorem circularTapeHalting_pspaceComplete :
    PSPACEComplete TapeInstance.enc circularTapeHalting := by sorry

end OptimalQueuingComplexity.Restless
