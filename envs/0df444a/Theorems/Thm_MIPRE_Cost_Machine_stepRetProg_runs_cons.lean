-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_stepRetProg_runs_cons
-- name    : MIPRE.Cost.Machine.stepRetProg_runs_cons
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:27:56.819984+00:00
-- url     : https://prove2.me/theorems/d1a3e6be-d281-49ed-9754-a2e021368664
-- title:
--   One return-step of the self-interpreter on a nonempty stack runs within cost $8S + 120$
-- statement:
--   We work in the ambient cost model of the formalization: data are binary trees (`Data`, from `nil` and `cons`), $\mathrm{size}(d)$ is the number of nodes of $d$, and $\mathrm{Eval}(\mathrm{env}, p, r, t)$ is the timed semantics (the program $p$ in the environment $\mathrm{env}$ halts with $r$ at cost exactly $t$; one unit per rule, plus the size of every value read by a variable or literal). The self-interpreter implements, as a program, the step function of a small-step evaluation machine whose configurations are encoded as data: an environment is a `cons`-chain of values, a stack a `cons`-chain of encoded frames, and a program $p$ is its tree encoding $\mathrm{toData}(p)$, a unary tag ($0$ to $6$ for `var`, `nil`, `cons`, `elim`, `let_`, `loop`, `const`) paired with the fields.
--
--   A frame of the machine is one of: `cons1 t env` (evaluating the head of a `cons`; next evaluate $t$ in $\mathrm{env}$), `cons2 a` (the head value $a$; next return $\texttt{cons}(a, v)$), `let1 b env` (next evaluate $b$ in $v :: \mathrm{env}$), `loop1 b env` (next dispatch on the value returned by the loop body: stop with `nil`, stop with $r$ on $\texttt{cons}(\texttt{nil}, r)$, or iterate on $\texttt{cons}(\texttt{cons}(\cdot,\cdot), v')$). Frames are encoded as data by $\mathrm{toData}(f) = \texttt{cons}(\mathrm{ofNat}(\mathrm{tag}), \mathrm{payload})$ with tags $0$ to $3$. The step on a "return $v$" control with a nonempty stack is the function $\mathrm{stepRet}(v, \mathrm{env}, \texttt{cons}(\mathrm{toData}(f), k))$ of the machine on data, and `stepRetProg` is the program implementing it, on the input $\texttt{cons}(v, \texttt{cons}(\mathrm{env}, \mathrm{kont}))$.
--
--   Let $v, \mathrm{env}$ be data, $f$ a frame and $k$ data (the rest of the stack). Write $S = \mathrm{size}(v) + \mathrm{size}(\mathrm{env}) + \mathrm{size}(\mathrm{toData}(f)) + \mathrm{size}(k)$. Then there is a cost $s$ with
--
--   $$ s \le 8S + 120 \quad\text{and}\quad \texttt{stepRetProg}\ \text{on}\ \texttt{cons}(v, \texttt{cons}(\mathrm{env}, \texttt{cons}(\mathrm{toData}(f), k)))\ \text{halts with}\ \mathrm{stepRet}(v, \mathrm{env}, \texttt{cons}(\mathrm{toData}(f), k))\ \text{at cost}\ s. $$
--
--   The return step is linear in the configuration size because no variable lookup is needed. With the empty-stack case (`stepRetProg_runs_nil`, cost at most $\mathrm{size}(v) + \mathrm{size}(\mathrm{env}) + 12$) and the evaluate step (`stepEvProg_runs`), it gives the step program of the self-interpreter (`stepProg_runs`), the body of the efficient universal machine's loop.
--
--   **Formalization Note**. The bound is `stepRetBound S = 8 * S + 120` of `MIPRE.Cost.Machine`; the stack is passed as $\texttt{cons}(\mathrm{toData}(f), k)$ with the top frame a genuine `Frame` (so that the four frame shapes, and the three shapes of $v$ under a `loop1` frame, can be enumerated) and $k$ arbitrary data. The environment stored in a frame is a `cons`-chain (`Data.list`), and in the iterating case of `loop1` the next environment is $v' :: \mathrm{tail}(\mathrm{env}')$, computed with one projection; this is the only place a size inequality ($\mathrm{size}(\mathrm{right}(d)) \le \mathrm{size}(d)$) enters.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Interpreter.lean#L733-L809; internal lemma of the formalization of blueprint lem:universal-tm (the return half of the self-interpreter's step program)

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open MIPRE.Cost.Prog

theorem MIPRE.Cost.Machine.stepRetProg_runs_cons (v env : Data) (f : Frame) (k : Data) :
    ∃ s ≤ stepRetBound (v.size + env.size + (Frame.toData f).size + k.size),
      stepRetProg.Runs (.cons v (.cons env (.cons (Frame.toData f) k)))
        (stepRet v env (.cons (Frame.toData f) k)) s := by sorry
