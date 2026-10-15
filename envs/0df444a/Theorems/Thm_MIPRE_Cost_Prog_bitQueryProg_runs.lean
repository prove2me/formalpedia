-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_bitQueryProg_runs
-- name    : MIPRE.Cost.Prog.bitQueryProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:28.912644+00:00
-- url     : https://prove2.me/theorems/14265c44-cf21-4141-acd3-bc3612338665
-- title:
--   Conditional correctness of the bit-query program: from a run of $c'$ on $(e,n)$ to answers about its output
-- statement:
--   We work in the ambient cost model: data are binary trees with $\mathrm{size}$ the number of nodes, programs (`Prog`) form a first-order language with de Bruijn variables, and $\rho \vdash p \Downarrow^{t} r$ (`Eval ρ p r t`) means that $p$ evaluated in the environment $\rho$ halts with result $r$ at cost $t$; a program *runs* on the input $v$ to $r$ at cost $t$ (`Prog.Runs`) when $[v] \vdash p \Downarrow^t r$. Every type $\alpha$ with a size-aware encoding (`SizedEncoding`) has an encoding map $\mathrm{enc} : \alpha \to \mathrm{Data}$ and the size $\|a\| = \mathrm{size}(\mathrm{enc}(a))$ (`esize`). Programs are encoded by their syntax trees; pairs by $\mathrm{enc}(a, b) = \mathrm{cons}(\mathrm{enc}(a), \mathrm{enc}(b))$, so that $\|(a, b)\| = \|a\| + \|b\| + 1$; bit strings as lists of bits; and natural numbers in binary, so that $\|m\| \le 4|m| + 1$ where $|m|$ is the bit length of $m$ (`Nat.size`).
--
--   A *universal machine* $U$ (`UniversalMachine`) consists of a closed program $u$ (`U.univ`) and a polynomial $p_U \in \mathbb{N}[X]$ (`U.bound`) such that, for every program $c$ and data $v, r$: if $c$ runs on $v$ to $r$ at cost $t$, then $u$ runs on $\mathrm{cons}(\mathrm{enc}(c), v)$ to $r$ at some cost at most $p_U(\|c\| + \mathrm{size}(v) + t)$; and if $u$ runs on $\mathrm{cons}(\mathrm{enc}(c), v)$ to $r$, then $c$ runs on $v$ to $r$.
--
--   The *bit-query program* $\beta_u$ (`bitQueryProg u`) takes as input the encoding of $(((c', e), n), m)$ — two programs $c'$ and $e$, a parameter $n$ of some encodable type $\alpha$, and a query $m \in \mathbb{N}$ — runs $u$ on $\mathrm{cons}(\mathrm{enc}(c'), \mathrm{enc}(e, n))$, that is, simulates $c'$ on the input $(e, n)$, and feeds the resulting string $y$ and the query $m$ to the bit-indexing program `bitAtProg`. The answer expected to a bit-query $m$ about $y$ is (`bitQueryAnswer y m`)
--
--   $$
--   \mathrm{ans}(y, m) = \begin{cases} \mathrm{enc}(y_m) & \text{if } m < |y|,\\ \underline{2} & \text{otherwise,}\end{cases}
--   $$
--
--   with $y_m$ the $m$-th bit of $y$ and $\underline 2$ the unary numeral $2$, the out-of-range marker.
--
--   **Theorem.** Let $U$ be a universal machine with program $u$ and polynomial $p_U$, let $c', e$ be programs, $n : \alpha$, $y \in \{0,1\}^*$, $m \in \mathbb{N}$, and suppose that $c'$ runs on $(e, n)$ to $y$ at cost $t$:
--
--   $$
--   [\mathrm{enc}(e, n)] \vdash c' \Downarrow^{t} \mathrm{enc}(y).
--   $$
--
--   Put $s = \|c'\| + \|e\| + \|n\| + t$ and let $B_U$ be the polynomial (`bitQueryBound U`)
--
--   $$
--   B_U(s) = p_U(s + 1) + (s+1)(s+534) + 2s + 29.
--   $$
--
--   Then there is a cost $T$ with
--
--   $$
--   T \le B_U(s)\cdot (|m| + 1)^2 \qquad\text{and}\qquad [\mathrm{enc}(((c', e), n), m)] \;\vdash\; \beta_u \;\Downarrow^{T}\; \mathrm{ans}(y, m).
--   $$
--
--   The string $y$ is given only implicitly, as the output of $c'$ on $(e, n)$; the theorem says that $\beta_u$ answers any bit-query about it at a cost polynomial in the sizes of the data and in the running time of $c'$, times $(|m|+1)^2$. It is the engine of `isSuccinctDesc_hardcode`: hardcoding $((c', e), n)$ into $\beta_u$ turns it into a succinct description of $y$ in the sense of blueprint `def:succinct`, which is how the proofs of the recursive compression lemma (`lem:recursive-compression`) and of the compressibility criterion describe the string computed at the next recursion level.
--
--   **Formalization Note** The parameter type $\alpha$ is any type with a `SizedEncoding` (in the compression lemmas it is $\mathbb{N}$ or a pair of naturals), and $n$ enters the bound only through $\|n\|$. The factor $(|m|+1)^2$ comes from the bit walk: it takes at most $|y| + 1$ iterations, each of cost at most $(\mathrm{size}(\mathrm{enc}(y)) + 534)(|m|+1)^2$ (`bitAtIter_le`), and both $|y|$ and $\mathrm{size}(\mathrm{enc}(y))$ are at most $t$, because a run of cost $t$ produces a result of size at most $t$ (`Eval.size_le`); this gives the term $(s+1)(s+534)$. The term $p_U(s+1)$ is the universal machine's overhead, its argument being $\|c'\| + \mathrm{size}(\mathrm{enc}(e,n)) + t = s + 1$. The term $2s + 29$ absorbs the copies of the arguments and of the intermediate values and the constant-cost rules, after using $x \le x(|m|+1)^2$ and $\|m\| \le 4|m|+1$. Only the forward direction is stated: a run of $c'$ yields a run of $\beta_u$; nothing is claimed about $\beta_u$ when $c'$ does not halt.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Succinct.lean#L73-L157; internal lemma of the formalization of blueprint def:succinct, used in lem:recursive-compression, https://vidick.github.io/MIPRE-formalization/blueprint/; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Definition 2.4 and Lemma 5.1

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
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Succinct

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open Polynomial

theorem MIPRE.Cost.Prog.bitQueryProg_runs (U : UniversalMachine) {α : Type*} [SizedEncoding α]
    (c' e : Prog) (n : α) (y : BitStr) (m : ℕ) {t : ℕ}
    (hrun : c'.Runs (encode (e, n)) (encode y) t) :
    ∃ T ≤ (bitQueryBound U).eval (esize c' + esize e + esize n + t) * (Nat.size m + 1) ^ 2,
      (bitQueryProg U.univ).Runs (encode (((c', e), n), m)) (bitQueryAnswer y m) T := by sorry
