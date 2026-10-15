-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_bitAtLoop_runs
-- name    : MIPRE.Cost.Prog.bitAtLoop_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:26:56.119255+00:00
-- url     : https://prove2.me/theorems/488e79b6-1d7c-47fc-bceb-ed40aa8f37c8
-- title:
--   The bit-query loop answers query $m$ about $y$ in at most $|y|+1$ iterations, each of cost quadratic in $|m|$
-- statement:
--   We work in the ambient cost model: data are binary trees with $\mathrm{size}$ the number of nodes, programs form a first-order language with de Bruijn variables, and $\rho \vdash p \Downarrow^{t} r$ (`Eval ρ p r t`) means that $p$ evaluated in the environment $\rho$ halts with result $r$ at cost $t$. A bit string $x \in \{0,1\}^*$ is encoded as the list $\mathrm{enc}(x)$ of its bits. For $\mathbf m \in \{0,1\}^*$ let $\mathrm{val}(\mathbf m) = \sum_i \mathbf m_i 2^i$ be its value read least significant bit first (`bitsVal`); the representation need not be canonical (trailing $0$ bits are allowed), and $|\mathbf m|$ is its length.
--
--   The bit-query program `bitAtProg` is the loop $\mathtt{loop}\ \mathtt{bitAtBody}$: starting from a state $\mathrm{cons}(\mathrm{enc}(y), \mathrm{enc}(\mathbf m))$ held in variable $0$, it repeatedly tests $\mathbf m$ for zero and, while it is nonzero, drops the head bit of $y$ and decrements $\mathbf m$ in binary; it stops with the head bit of $y$ when $\mathbf m$ reaches zero, and with the out-of-range marker when $y$ is exhausted. The answer it must compute is (`bitQueryAnswer y m`)
--
--   $$
--   \mathrm{ans}(y, m) = \begin{cases} \mathrm{enc}(y_m) & \text{if } m < |y|,\\ \underline{2} & \text{otherwise,}\end{cases}
--   $$
--
--   where $y_m$ is the $m$-th bit of $y$ (counting from $0$) and $\underline 2$ is the unary numeral $2$ (`Data.ofNat 2`), the out-of-range marker.
--
--   The cost of one iteration on a string of encoded size at most $s_y$ and an index of $L$ bits is bounded by (`bitAtIter`)
--
--   $$
--   \mathrm{bitAtIter}(s_y, L) = s_y + 8L + \mathrm{zeroBound}(L) + \mathrm{decBound}(L) + 20,
--   $$
--
--   where $\mathrm{zeroBound}(L) = (L+1)(4L+9)$ bounds the cost of a zero test and $\mathrm{decBound}(L) = (L+2)(60L+100)$ the cost of a decrement on an index of $L$ bits.
--
--   **Theorem.** Let $m \in \mathbb{N}$, let $y, \mathbf m \in \{0,1\}^*$ with $\mathrm{val}(\mathbf m) = m$, let $\rho$ be any environment, and let $s_y, L \in \mathbb{N}$ with $\mathrm{size}(\mathrm{enc}(y)) \le s_y$ and $|\mathbf m| = L$. Then there is a cost $t$ such that
--
--   $$
--   t \le (|y| + 1)\cdot \mathrm{bitAtIter}(s_y, L) \qquad\text{and}\qquad \mathrm{cons}(\mathrm{enc}(y), \mathrm{enc}(\mathbf m)) :: \rho \;\vdash\; \mathtt{bitAtProg} \;\Downarrow^{t}\; \mathrm{ans}(y, m).
--   $$
--
--   This is the loop invariant of the bit-query program, proved by induction on the queried index $m$ with the string, the representation of the index and the environment generalized; the corollary `bitAtProg_runs` instantiates it with the canonical representation $\mathbf m = \mathrm{bits}(m)$, $s_y = \mathrm{size}(\mathrm{enc}(y))$, $L = |m|$ (the bit length of $m$) and the empty environment. Through `bitQueryProg_runs` and `isSuccinctDesc_hardcode` it is what lets the recursive compression argument answer bit-queries about an implicitly given string within the succinctness budget of blueprint `def:succinct`: the factor $(|m|+1)^2$ in that budget is the quadratic growth of $\mathrm{bitAtIter}$ in $L$ (`bitAtIter_le`: $\mathrm{bitAtIter}(s_y, L) \le (s_y + 534)(L+1)^2$).
--
--   **Formalization Note** The statement is about `Eval` in an environment whose head is the state and whose tail $\rho$ is arbitrary and inert; the loop rule of the semantics replaces variable $0$ by the new state at each iteration and keeps the tail. The index is an arbitrary bit string $\mathbf m$ of value $m$ (`bitsVal mb = m`) rather than `Nat.bits m`, because the decrement may leave trailing zeros; the bounds are in terms of the slack parameters $s_y$ (any upper bound on the size of the encoded string) and $L$ (the length of the index, which the decrement preserves). Each zero test and decrement copies the index, which is why $\mathrm{zeroBound}$ and $\mathrm{decBound}$ are quadratic in $L$, and each iteration also copies the remaining string, whence the term $s_y$. In the out-of-range case the result $\underline 2 = \mathrm{cons}(\mathrm{nil}, \mathrm{cons}(\mathrm{nil},\mathrm{nil}))$ has size $5$. The constants $8L$, $20$, $4L+9$ and $60L+100$ are those of the Lean definitions `bitAtIter`, `zeroBound` and `decBound`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/BitQuery.lean#L147-L209; internal lemma of the formalization of blueprint def:succinct (the bit-query program), https://vidick.github.io/MIPRE-formalization/blueprint/; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Definition 2.4

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog

theorem MIPRE.Cost.Prog.bitAtLoop_runs (m : ℕ) (y mb : BitStr) (hmb : bitsVal mb = m) (env : Env) (sy L : ℕ)
    (hsy : (encode y).size ≤ sy) (hL : mb.length = L) :
    ∃ t ≤ (y.length + 1) * bitAtIter sy L,
      Eval (.cons (encode y) (encode mb) :: env) bitAtProg (bitQueryAnswer y m) t := by sorry
