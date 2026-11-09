-- Prove2me | Theorems.Thm_FourBlockIP_FPT_theorem_2
-- name    : FourBlockIP.FPT.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:03.006611+00:00
-- url     : https://prove2.me/theorems/ee69b90b-a9ab-47ff-b106-cc6731b3f62e
-- title:
--   Theorem 2 (corrected: degenerate parameters floored at 1, logs of (·+2))
-- statement:
--   There exist one program $P$ and one absolute natural constant $a\ge2$, both chosen before every 4-block instance and every finite separable convex objective. Let $r,s,t,p,n,\Delta$ be arbitrary naturals. The global blocks $A_0,C_i$ and the integer right-hand sides are unrestricted; only the entries of $B_i,D_i$ have absolute value at most $\Delta$. Bounds $l,u$ may be inconsistent. Define
--
--   $$r'=\max(r,1),\quad p'=\max(p,1),\quad\Delta'=\max(\Delta,1),\quad N=\max(t,1)\max(n,1),\quad D=\max_j|u_j-l_j|,$$
--
--   where $D=0$ for an empty variable space, and
--
--   $$E=(a(r'+s)\Delta')^{r'(r'+s)}p'+a(p')^2\lfloor\log_2(p'+2)\rfloor.$$
--
--   With only comparisons of objective values at integer vectors, the run of $P$ on the block-sparse input halts in at most
--
--   $$2^E aN\lfloor\log_2(N+2)\rfloor^a\lfloor\log_2(D+2)\rfloor^a$$
--
--   unit arithmetic/query operations. Its output is $[0]$ if and only if the IP is infeasible; otherwise it returns a leading $1$ followed by an integer vector satisfying all 4-block equations and bounds and minimizing the objective against every feasible integer vector.
--
--   This is the full separable convex headline result with the declared zero-parameter correction, including cost, halting and attained optimality in one statement.
--
--   Differences from the source:
--   - correction: the printed bound ranges over zero parameters and unsaturated logarithms → r,p,Delta are floored at one, N=max(t,1)max(n,1), and all logarithm arguments gain two; reason: C1: with zero matrices, f=0, n=2,t=1,D=2 and growing s, setting r=0 or p=0 or Delta=0 makes the printed time independent of s although changing an unread local right-hand side from zero to one changes feasibility; zero local size and small logs also need constant-size padding
--   - reading: O((r+s)Delta) to the power r(r+s) times p plus p squared log p in the exponent → one absolute constant in the coefficient base and a multiplier on p squared log p; reason: R1: the derivations on pp. 8–9 and 21 place an O on the latter term as well
--   - reading: time counts arithmetic operations and comparison oracle queries → one uniform restricted two-sorted RAM with integer quotient/remainder, exact reals, floor, indirect integer/real memory and unit-cost comparison bits; reason: R2: this specifies the source arithmetic convention; preparing queries is charged, malformed lengths answer false, rational program literals only, no bit-length conclusion
--   - encoding: a vector of p+tn variables and a 4-block matrix → global coordinates plus indexed local coordinates, encoded in block-sparse order; reason: finite reindexing preserves every instance and avoids a dense matrix input whose size would exceed the runtime bound
-- source:
--   Martin Koutecký, Alexandra Lassota, Koen Ligthart, 4-Block Integer Programming is in FPT, STOC 2027 submission #392 (October 2026), Theorem 2, p. 3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/392.pdf

import Mathlib
import Definitions.Def_FourBlockIP_FPT_Framework

namespace FourBlockIP.FPT

/-- Theorem 2, p. 3 (restated p. 8), corrected by C1. Uniform program and
absolute constant, chosen before every instance and objective. R1 fixes the
scope of O in the exponent; R2 fixes the unit arithmetic/comparison RAM.
No assumption l≤u; no bounds on A0,C,b; no bit-complexity claim. -/
theorem theorem_2 : ∃ P : Program, ∃ c : ℕ, 2 ≤ c ∧
    ∀ (I : Instance) (f : (Var I → ℝ) → ℝ), SepConvex f →
      ∃ t,
        let st := run P (blockOracle I f) (encode I) [] t
        halted P st = true ∧ st.cost ≤ goalBound c I ∧
          CorrectOutput I f (output st) := by sorry

end FourBlockIP.FPT
