-- Prove2me | Theorems.Thm_MIPRE_Cost_isSuccinctDesc_hardcode
-- name    : MIPRE.Cost.isSuccinctDesc_hardcode
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:24.763974+00:00
-- url     : https://prove2.me/theorems/a3c4dc42-4c18-45a5-97e1-fc14eb9b0771
-- title:
--   Hardcoding into the bit-query program gives a succinct description of the output of a fast program
-- statement:
--   We work in the ambient cost model: data are binary trees with $\mathrm{size}$ the number of nodes, programs (`Prog`) form a first-order language with de Bruijn variables, $\rho \vdash p \Downarrow^{t} r$ (`Eval ρ p r t`) means that $p$ evaluated in the environment $\rho$ halts with result $r$ at cost $t$, and a program *runs* on $v$ to $r$ at cost $t$ when $[v] \vdash p \Downarrow^t r$ (`Prog.Runs`). A type with a size-aware encoding (`SizedEncoding`) has an encoding $\mathrm{enc}$ and sizes $\|a\| = \mathrm{size}(\mathrm{enc}(a))$; pairs are encoded by $\mathrm{enc}(a,b) = \mathrm{cons}(\mathrm{enc}(a), \mathrm{enc}(b))$, natural numbers in binary, with $|m|$ the bit length of $m$, and bit strings as lists of bits.
--
--   **Succinct descriptions** (blueprint `def:succinct`, after [MNY, Definition 2.4]). A program $c$ with parameter $n \in \mathbb{N}$ is a *succinct description* of $x \in \{0,1\}^*$, written $\mathrm{IsSuccinctDesc}(c, n, x)$, if
--
--   1. $c$ is closed (`WellScoped 1`: it reads only its input, variable $0$);
--   2. $|x| \le 2^n$;
--   3. for every $m \in \mathbb{N}$, $c$ runs on $\mathrm{enc}(m)$ to $\mathrm{ans}(x, m)$ at some cost at most $(n+1)(|m|+1)^2$, where $\mathrm{ans}(x, m)$ is $\mathrm{enc}(x_m)$ if $m < |x|$ and the unary numeral $\underline 2$ otherwise (`bitQueryAnswer`).
--
--   **The s-m-n map** (`hardcode`). For a program $p$ and a datum $d$, $\mathrm{hardcode}(p, d) = \mathtt{let}\ \mathrm{cons}(\mathtt{const}\ d, \mathtt{var}\ 0)\ \mathtt{in}\ p$ is the program that, on an input $x$, runs $p$ on the pair $\mathrm{cons}(d, x)$.
--
--   **The bit-query program.** Let $U$ be a universal machine (`UniversalMachine`): a closed program $u$ with an overhead polynomial $p_U$ such that a run of $c$ on $v$ at cost $t$ yields a run of $u$ on $\mathrm{cons}(\mathrm{enc}(c), v)$ with the same result at cost at most $p_U(\|c\| + \mathrm{size}(v) + t)$, and $u$ halts only when the simulated program does. The bit-query program $\beta_u$ (`bitQueryProg u`) on the encoding of $(((c', e), n'), m)$ simulates $c'$ on $(e, n')$ through $u$ and returns the $m$-th bit of the output (or the marker). Its cost is governed by the polynomial (`bitQueryBound U`) $B_U(s) = p_U(s+1) + (s+1)(s+534) + 2s + 29$.
--
--   **Theorem.** Let $U$ be a universal machine, $\alpha$ a type with a size-aware encoding, $c'$ and $e$ programs, $n' : \alpha$, $n \in \mathbb{N}$, $y \in \{0,1\}^*$ and $t \in \mathbb{N}$. Assume
--
--   1. $[\mathrm{enc}(e, n')] \vdash c' \Downarrow^{t} \mathrm{enc}(y)$: the program $c'$ runs on the input $(e, n')$ to the string $y$ at cost $t$;
--   2. $t \le 2^n$;
--   3. the budget condition
--   $$
--   B_U\bigl(\|c'\| + \|e\| + \|n'\| + t\bigr) + \bigl(\|c'\| + \|e\| + 1 + \|n'\| + 1\bigr) + 4 \;\le\; n + 1,
--   $$
--   in which $\|c'\| + \|e\| + 1 + \|n'\| + 1 = \mathrm{size}(\mathrm{enc}((c', e), n'))$ is the size of the datum to be hardcoded.
--
--   Then
--
--   $$
--   \mathrm{IsSuccinctDesc}\bigl(\mathrm{hardcode}(\beta_u,\ \mathrm{enc}((c', e), n')),\ n,\ y\bigr):
--   $$
--
--   the bit-query program with $((c', e), n')$ hardcoded is a succinct description of $y$ with parameter $n$.
--
--   This is the step of the recursive compression argument ([MNY, Lemma 5.1], blueprint `lem:recursive-compression`; likewise for the compressibility criterion `lem:compressible-criterion`) that manufactures, inside the self-referential decider, a *genuine* succinct description of the string computed at the next recursion level — the output $y$ of the fixed-point program $c'$ on $(e, n')$ — so that the guarantees of the compression procedure, which hold only on genuine descriptions, apply to it. There, $n'$ is the next level ($2n+1$, or a pair of levels), the bound $t \le 2^n$ comes from the polynomial time bound of the decider, which is at most $n + 1 \le 2^n$ above a threshold, and the budget condition is discharged by the threshold lemma `exists_threshold`: for $n \ge 2^{K + 1 + \|e\|}$, with $K$ depending on the overhead polynomial, every polynomial in $\|e\| + |n|$ is at most $n + 1$.
--
--   **Formalization Note** `IsSuccinctDesc` differs from [MNY, Definition 2.4] in its time bound: $(n+1)(|m|+1)^2$ instead of $n$, since in a model that charges for reading its input a bound independent of $|m|$ is vacuous for $|m| > n$ (module docstring of `MIPRE.Foundations.Compression`). The hardcoded parameter $n' : \alpha$ is independent of the description's parameter $n \in \mathbb{N}$, and $\alpha$ may be any encodable type. The description's cost on a query $m$ is, by `hardcode_time`, the cost of $\beta_u$ on the pair plus $\mathrm{size}(\mathrm{enc}((c',e),n')) + \mathrm{size}(\mathrm{enc}(m)) + 3$, and $\mathrm{size}(\mathrm{enc}(m)) \le 4|m| + 1$; the summand $+4$ of the budget condition is what absorbs this overhead after multiplication by $(|m|+1)^2$. The length clause follows from $|y| \le \mathrm{size}(\mathrm{enc}(y)) \le t \le 2^n$, since a run of cost $t$ has a result of size at most $t$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Succinct.lean#L159-L187; internal lemma of the formalization of blueprint def:succinct, used in lem:recursive-compression, https://vidick.github.io/MIPRE-formalization/blueprint/; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Definition 2.4 and Lemma 5.1

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
open Polynomial

theorem MIPRE.Cost.isSuccinctDesc_hardcode (U : UniversalMachine) {α : Type*} [SizedEncoding α]
    (c' e : Prog) (n' : α) (n : ℕ) (y : BitStr)
    {t : ℕ} (hrun : c'.Runs (encode (e, n')) (encode y) t) (hlen : t ≤ 2 ^ n)
    (hbudget : (bitQueryBound U).eval (esize c' + esize e + esize n' + t) +
      (esize c' + esize e + 1 + esize n' + 1) + 4 ≤ n + 1) :
    IsSuccinctDesc (hardcode (Prog.bitQueryProg U.univ) (encode ((c', e), n'))) n y := by sorry
