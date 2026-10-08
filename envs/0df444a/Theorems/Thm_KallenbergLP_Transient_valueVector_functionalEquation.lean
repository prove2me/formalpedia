-- Prove2me | Theorems.Thm_KallenbergLP_Transient_valueVector_functionalEquation
-- name    : KallenbergLP.Transient.valueVector_functionalEquation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:39:41.124011+00:00
-- url     : https://prove2.me/theorems/393b7ca1-0282-4310-a627-fd3efdad8e70
-- title:
--   Theorem 3.2.2 — a p-summable TMD-value-vector satisfies the optimality equation
-- statement:
--   Consider a finite Markov decision model with substochastic transitions $p_{iaj}$ and real rewards $r_{ia}$ satisfying Assumption 3.2.1: every policy has an expected total reward $v_i(R)\in[-\infty,+\infty]$ for every initial state. Let $v_i=\sup_Rv_i(R)$ be the TMD-value-vector, with values in $[-\infty,+\infty]$. Call $x\in[-\infty,+\infty]^E$ **p-summable** if, with $0\cdot c:=0$, no sum $\sum_jp_{iaj}x_j$ ($a\in A(i)$, $i\in E$) contains both $+\infty$ and $-\infty$.
--
--   If $v$ is p-summable, then $v$ satisfies the functional equation
--
--   $$\begin{cases}x_i=\max_{a\in A(i)}\big\{r_{ia}+\sum_jp_{iaj}x_j\big\},& i\in E,\\ x\ \text{is p-summable.}\end{cases}$$
--
--   The p-summability hypothesis cannot be dropped: in the book's Example 3.2.1 the value vector has entries $+\infty$ and $-\infty$ reached from the same action, and the right-hand side is undefined.
--
--   **Formalization Note** The sum is computed in `EReal`, where $0\cdot(\pm\infty)=0$ as in the book; under p-summability no $(+\infty)+(-\infty)$ occurs. The second clause of the conclusion repeats the hypothesis, as in the book's statement.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 37, Assumption 3.2.1; p. 39, Definition 3.2.1 and Theorem 3.2.2

import Definitions.Def_KallenbergLP_Transient_TotalReward
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- Theorem 3.2.2: under Assumption 3.2.1, a p-summable TMD value vector solves the
extended-real functional equation `x_i = max_a {r_ia + ∑_j p_iaj x_j}`, `x` p-summable. -/
theorem valueVector_functionalEquation
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (r : Fin N → α → ℝ)
    (hreward : TotalRewardExists M r)
    (hv : PSummable M (valueVector M r)) :
    (∀ i : Fin N, valueVector M r i = bellmanRHS M r (valueVector M r) i) ∧
      PSummable M (valueVector M r) := by sorry

end KallenbergLP.Transient
