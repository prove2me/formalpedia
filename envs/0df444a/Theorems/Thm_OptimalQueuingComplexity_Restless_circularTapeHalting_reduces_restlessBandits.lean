-- Prove2me | Theorems.Thm_OptimalQueuingComplexity_Restless_circularTapeHalting_reduces_restlessBandits
-- name    : OptimalQueuingComplexity.Restless.circularTapeHalting_reduces_restlessBandits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T12:38:32.746976+00:00
-- url     : https://prove2.me/theorems/be3bbaf6-59ba-46d0-b14c-669bc807eb86
-- title:
--   Theorem 4 (proof, reduction) — circular-tape halting reduces to RESTLESS BANDITS
-- statement:
--   Let CIRCULAR-TAPE HALTING be the problem of deciding whether the circular-tape process (squares $1,\dots,n$, values in $\{1,\dots,A\}$, rule $F$ with $F(1,1)=1$) started from a given configuration eventually has all squares equal to $1$. Let RESTLESS BANDITS be the decision problem: given $n \ge 1$ bandits on a finite state space $S$ with deterministic rules $P$ (played) and $Q$ (not played), rational costs $c, d$, initial states and a rational threshold $K$, is there a policy $\pi : S^n \to \{1,\dots,n\}$ whose average cost $\limsup_{T\to\infty} \frac1T\sum_{t=1}^T C(t)$ is at most $K$? Then
--   $$\text{CIRCULAR-TAPE HALTING} \;\le_p\; \text{RESTLESS BANDITS (deterministic transition rules)},$$
--   that is, there is a map $f$ from tape instances to bandit instances, computable in polynomial time on the encodings, such that for every tape instance $I$, the process of $I$ halts (and $I$ is well formed) if and only if $f(I)$ is a yes-instance of RESTLESS BANDITS.
--
--   This is the second step of the proof of Theorem 4. Combined with the PSPACE-hardness of CIRCULAR-TAPE HALTING it gives the theorem.
--
--   **Formalization Note.** The statement is about the existence of a reduction, not about the paper's specific construction (segments, layers, trapping state); any polynomial-time reduction proves it.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), pp. 303–304, proof of Theorem 4 (reduction)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Definitions.Def_OptimalQueuingComplexity_Restless_circularTapeHalting
import Definitions.Def_OptimalQueuingComplexity_Restless_restlessBandits

namespace OptimalQueuingComplexity.Restless

/-- Papadimitriou & Tsitsiklis 1999, pp. 303–304, proof of Theorem 4 (reduction): circular-tape
halting polynomial-time many-one reduces to the decision version of RESTLESS BANDITS with
deterministic transition rules. -/
theorem circularTapeHalting_reduces_restlessBandits :
    PolyReduces TapeInstance.enc circularTapeHalting Instance.enc restlessBandits := by sorry

end OptimalQueuingComplexity.Restless
