-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_isZeroProg_runs
-- name    : MIPRE.Cost.Prog.isZeroProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:09.31647+00:00
-- url     : https://prove2.me/theorems/cc15c3b8-ff14-4fd5-bc79-98da1dfd5a98
-- title:
--   Zero test on a binary numeral runs within cost $(|\ell|+1)(S+8)$
-- statement:
--   We work in the ambient cost model of the formalization: data are binary trees (`Data`, built from `nil` and `cons`), $\mathrm{size}(d)$ is the number of nodes of $d$, and a bit string $\ell \in \{0,1\}^*$ is encoded as the `cons`-chain of its bits ($0 \mapsto$ `nil`, $1 \mapsto$ `cons nil nil`). A bit string is read as a binary numeral, least significant bit first. The timed semantics $\mathrm{Eval}(\mathrm{env}, p, r, t)$ says that the program $p$, run in the environment $\mathrm{env}$ (a list of data values, variable $0$ first), halts with result $r$ at cost exactly $t$; one unit is charged per evaluation rule, and reading a variable or a literal additionally costs the size of the value read.
--
--   Let $\ell \in \{0,1\}^*$, let $\mathrm{env}$ be any environment, and let $S \in \mathbb{N}$ be a bound with $\mathrm{size}(\mathrm{encode}(\ell)) \le S$. Let `isZeroProg` be the fixed zero-test program (a `loop` whose body inspects the leading bit of the state and either stops or continues with the tail). Then there is a cost $t$ with
--
--   $$ t \le (|\ell| + 1)\,(S + 8) \quad\text{and}\quad \mathrm{Eval}\bigl(\mathrm{encode}(\ell) :: \mathrm{env},\ \texttt{isZeroProg},\ \mathrm{encode}(\textstyle\bigvee_i \ell_i),\ t\bigr), $$
--
--   that is, with its input $\mathrm{encode}(\ell)$ in variable $0$ (and arbitrary further variables), the program halts with the encoded Boolean "some bit of $\ell$ is $1$": the result is `nil` exactly when the numeral $\ell$ has value $0$, and `cons nil nil` otherwise.
--
--   This is one of the two arithmetic primitives of the bit-query program `bitAtProg` of the succinct-description machinery: that program walks a string while decrementing a binary index $m$, and tests the index for zero at each step. With $S = 4|\ell| + 1$ (the size of an encoded bit string of length $|\ell|$ is at most $4|\ell|+1$) the bound becomes the quantity `zeroBound` $= (|\ell|+1)(4|\ell|+9)$ of that analysis, one of the sources of the quadratic factor $(|m|+1)^2$ in the time budget of a succinct description.
--
--   **Formalization Note**. The statement is about `MIPRE.Cost.Prog.isZeroProg` in the model `MIPRE.Cost.Eval`; the result is `encode (l.any id)`, the encoding of the Boolean `l.any id` (`false` $\mapsto$ `nil`, `true` $\mapsto$ `cons nil nil`). The bound is quadratic rather than linear because the loop state (the remaining string) is copied, at a cost equal to its size, at each iteration; $S$ is any number dominating that size, so that the bound is a single product $(|\ell|+1)(S+8)$. The extra environment entries `env` are inert because the program is closed (well-scoped in one variable).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Numeric.lean#L150-L181; internal lemma of the formalization of blueprint def:succinct (the zero test on binary indices used by the bit-indexing program `bitAtProg`)

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog

theorem MIPRE.Cost.Prog.isZeroProg_runs (l : BitStr) (env : Env) (S : ℕ) (hS : (encode l).size ≤ S) :
    ∃ t ≤ (l.length + 1) * (S + 8),
      Eval (encode l :: env) isZeroProg (encode (l.any id)) t := by sorry
