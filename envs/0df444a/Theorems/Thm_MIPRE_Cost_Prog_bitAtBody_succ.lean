-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_bitAtBody_succ
-- name    : MIPRE.Cost.Prog.bitAtBody_succ
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:26:54.66628+00:00
-- url     : https://prove2.me/theorems/193d0178-d63e-4e6d-81fb-632c5586ac9d
-- title:
--   One iteration of the bit-query walk with a nonzero index: continue with the tail and the decremented index
-- statement:
--   We work in the ambient cost model of the formalization. Data are binary trees (`Data`, built from $\mathrm{nil}$ and $\mathrm{cons}$), and $\mathrm{size}(d)$ is the number of nodes of $d$. Programs (`Prog`) form a small first-order language with de Bruijn variables, and we write $\rho \vdash p \Downarrow^{t} r$ for the timed big-step semantics `Eval ρ p r t`: the program $p$, evaluated in the environment $\rho$ (a list of values, variable $0$ first), halts with result $r$ at cost $t$. A bit string $x \in \{0,1\}^*$ is encoded as the list $\mathrm{enc}(x)$ of its bits, $\mathrm{enc}(b :: x) = \mathrm{cons}(\mathrm{enc}(b), \mathrm{enc}(x))$, and a binary index is such a bit string read least significant bit first.
--
--   The bit-query program `bitAtProg`, which returns the $m$-th bit of a string, is a loop whose body `bitAtBody` acts on a state $\mathrm{cons}(\mathrm{enc}(y), \mathrm{enc}(\mathbf m))$ made of the remaining string $y$ and the remaining binary index $\mathbf m$. The body first checks whether $y$ is exhausted; otherwise it calls the zero test `isZeroProg` on $\mathbf m$ and, if $\mathbf m$ is nonzero, calls the decrement `decProg` on $\mathbf m$ and signals that the loop should continue with the tail of $y$ and the decremented index. This lemma is the exact evaluation of the body in that last case.
--
--   Let $b \in \{0,1\}$ and $y_s, \mathbf m, \mathbf m' \in \{0,1\}^*$, let $t_z, t_d \in \mathbb{N}$, and assume:
--
--   1. some bit of $\mathbf m$ equals $1$ (`mb.any id = true`), i.e. the index is nonzero;
--   2. $[\mathrm{enc}(\mathbf m)] \vdash \mathtt{isZeroProg} \Downarrow^{t_z} \mathrm{enc}(\mathrm{any}(\mathbf m))$: the zero test, run on $\mathbf m$ alone, returns the encoded Boolean "some bit of $\mathbf m$ is $1$" (so here $\mathrm{enc}(\mathrm{true}) = \mathrm{cons}(\mathrm{nil},\mathrm{nil})$) at cost $t_z$;
--   3. $[\mathrm{enc}(\mathbf m)] \vdash \mathtt{decProg} \Downarrow^{t_d} \mathrm{enc}(\mathbf m')$: the decrement program, run on $\mathbf m$ alone, returns the bit string $\mathbf m'$ at cost $t_d$.
--
--   Then, in the one-element environment holding the state $\mathrm{cons}(\mathrm{enc}(b :: y_s), \mathrm{enc}(\mathbf m))$,
--
--   $$
--   [\mathrm{cons}(\mathrm{enc}(b :: y_s), \mathrm{enc}(\mathbf m))] \;\vdash\; \mathtt{bitAtBody} \;\Downarrow^{\,2\,\mathrm{size}(\mathrm{enc}(\mathbf m)) + t_z + t_d + \mathrm{size}(\mathrm{enc}(y_s)) + 14}\; \mathrm{cons}\bigl(\mathrm{cons}(\mathrm{nil},\mathrm{nil}),\, \mathrm{cons}(\mathrm{enc}(y_s), \mathrm{enc}(\mathbf m'))\bigr).
--   $$
--
--   The result is the loop's "continue" signal: a nonzero flag $\mathrm{cons}(\mathrm{nil},\mathrm{nil})$ followed by the new state $(y_s, \mathbf m')$, so that the enclosing loop proceeds with the head bit $b$ dropped and the index replaced by $\mathbf m'$.
--
--   Together with the two other cases of the body — an exhausted string (`bitAtBody_nil`, which stops with the out-of-range marker) and a zero index (`bitAtBody_zero`, which stops with the head bit) — this is the inductive step of `bitAtLoop_runs`, the correctness and cost analysis of `bitAtProg`. That analysis is where the bit-query program of the recursive compression argument gets its cost quadratic in $|m|$, and hence where the succinctness budget $(n+1)(|m|+1)^2$ of `IsSuccinctDesc` (blueprint `def:succinct`) comes from.
--
--   **Formalization Note** The statement is in the timed big-step semantics `Eval` of `MIPRE.Foundations.Cost.Basic`: one unit per rule, plus the size of the value for each variable read (`var`) or literal (`const`), since values are copied when read. The cost $2\,\mathrm{size}(\mathrm{enc}(\mathbf m)) + t_z + t_d + \mathrm{size}(\mathrm{enc}(y_s)) + 14$ is exact, not an upper bound: the index is copied twice (once for each call, made through `callVar`, which binds a copy of a variable as the callee's input), the tail $y_s$ once, and the fourteen remaining units are the rule costs of the body — three `elim`s, three `let`s (the body's own and one inside each call), the unit part of three variable reads, and the five constructor rules building the flag and the two pairs of the result. The hypotheses on `isZeroProg` and `decProg` are the runs themselves, with arbitrary costs $t_z, t_d$; the lemma uses neither their specifications nor the fact that $\mathbf m'$ represents the predecessor of $\mathbf m$, which enter only in `bitAtLoop_runs`. The zero test's result is written $\mathrm{enc}(\mathrm{any}(\mathbf m))$ (`encode (mb.any id)`); hypothesis 1 identifies it with $\mathrm{enc}(\mathrm{true})$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/BitQuery.lean#L128-L145; internal lemma of the formalization of blueprint def:succinct (the bit-query program), https://vidick.github.io/MIPRE-formalization/blueprint/; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Definition 2.4

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

theorem MIPRE.Cost.Prog.bitAtBody_succ (b : Bool) (ys mb mb' : BitStr) (hz : mb.any id = true) (tz td : ℕ)
    (hzr : Eval [encode mb] isZeroProg (encode (mb.any id)) tz)
    (hd : Eval [encode mb] decProg (encode mb') td) :
    Eval [.cons (encode (b :: ys)) (encode mb)] bitAtBody
      (.cons (.cons .nil .nil) (.cons (encode ys) (encode mb')))
      (2 * (encode mb).size + tz + td + (encode ys).size + 14) := by sorry
