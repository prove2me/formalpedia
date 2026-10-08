-- Prove2me | Theorems.Thm_GTWSched_NPC_theorem_1_reduction
-- name    : GTWSched.NPC.theorem_1_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:50:22.179617+00:00
-- url     : https://prove2.me/theorems/957c0c5e-5dda-44d7-ad1c-87e7ce993c0e
-- title:
--   Proof of THEOREM 1, pp. 336–337 — the instance D has a schedule of cost ≤ k iff X has an even-odd partition
-- statement:
--   Let $X=\{x_1,\dots,x_{2n}\}$ be an instance of even-odd partition ($n\ge1$, positive integers, $x_i<x_{i+1}$) with $x_1>1$. Build the instance D of total discrepancy with $2n+2$ tasks $T_0,\dots,T_{2n+1}$:
--   1. lengths $l_0=x_1-1$, $l_i=x_i$ for $1\le i\le 2n$, $l_{2n+1}=2$;
--   2. preferred midtimes $M_j=M=\sum_{i=0}^{2n}l_i/2$ for $0\le j\le 2n$, and $M_{2n+1}=2M+l_{2n+1}/2$;
--   3. threshold $k=\sum_{i=1}^n(l_{2i}+l_{2i-1})(n-i+\tfrac12)+l_0\,n$.
--
--   Then
--   $$\exists\ \text{schedule } S \text{ of D with } \sum_{j=0}^{2n+1}|m_j(S)-M_j|\le k\iff X \text{ has an even-odd partition with equal sums.}$$
--
--   **Formalization Note** The instance D is real-valued (`dLen`, `dMid`, `dK`), since $M$ and $k$ can be half-integers; schedules have real, nonnegative starting times, and nonnegativity is essential here (the tasks of $A(S')$ must fit between $0$ and $M-l_0/2$). The paper's "without loss of generality we assume that $x_1>1$" is a hypothesis.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), pp. 336–337, proof of THEOREM 1

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems

namespace GTWSched.NPC

/-- Proof of THEOREM 1, pp. 336–337: for an even-odd partition instance `X` with `x₁ > 1`, the
instance D (lengths `l₀ = x₁ − 1`, `lᵢ = xᵢ`, `l₂ₙ₊₁ = 2`; midtimes `M = ∑ᵢ₌₀²ⁿ lᵢ/2` for
`T₀, …, T₂ₙ` and `2M + l₂ₙ₊₁/2` for `T₂ₙ₊₁`; threshold `k`) has a schedule of cost at most `k`
iff `X` has an even-odd partition into two parts of equal sum. -/
theorem theorem_1_reduction (x : List ℕ) (hx : EOInstance x) (hx1 : 1 < x.getD 0 0) :
    EOYes x ↔ TDYesReal (dLen x) (dMid x) (dK x) := by sorry

end GTWSched.NPC
