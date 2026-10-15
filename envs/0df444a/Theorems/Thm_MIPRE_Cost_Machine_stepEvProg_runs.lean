-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_stepEvProg_runs
-- name    : MIPRE.Cost.Machine.stepEvProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:27:57.58124+00:00
-- url     : https://prove2.me/theorems/d6d68e15-3e45-4b09-bf72-9526fceb55e9
-- title:
--   One evaluate-step of the self-interpreter runs within cost $(S+1)(S+30)+100$ in the configuration size $S$
-- statement:
--   We work in the ambient cost model of the formalization: data are binary trees (`Data`, from `nil` and `cons`), $\mathrm{size}(d)$ is the number of nodes of $d$, and $\mathrm{Eval}(\mathrm{env}, p, r, t)$ is the timed semantics (the program $p$ in the environment $\mathrm{env}$ halts with $r$ at cost exactly $t$; one unit per rule, plus the size of every value read by a variable or literal). The self-interpreter implements, as a program, the step function of a small-step evaluation machine whose configurations are encoded as data: an environment is a `cons`-chain of values, a stack a `cons`-chain of encoded frames, and a program $p$ is its tree encoding $\mathrm{toData}(p)$, a unary tag ($0$ to $6$ for `var`, `nil`, `cons`, `elim`, `let_`, `loop`, `const`) paired with the fields.
--
--   A configuration of the evaluation machine whose control is "evaluate the program $p$", with environment $\mathrm{env}$ and stack $\mathrm{kont}$ (both as data), is handled by the step function $\mathrm{stepEv}(\mathrm{toData}(p), \mathrm{env}, \mathrm{kont})$ of the machine on data: by the tag of $p$, it returns the looked-up variable, `nil` or the literal (controls "return $v$"); or it pushes a frame and moves to a subterm (for `cons`, `let_`, `loop`); or, for `elim i n c`, it inspects the $i$-th variable and continues with $n$, or with $c$ in the environment extended by the two components. The program `stepEvProg` implements this step: its input is the triple $\texttt{cons}(\mathrm{toData}(p), \texttt{cons}(\mathrm{env}, \mathrm{kont}))$.
--
--   Let $p$ be a program and $\mathrm{env}, \mathrm{kont}$ data. Write $|p| = \mathrm{size}(\mathrm{toData}(p))$ for the size of the program and $S = |p| + \mathrm{size}(\mathrm{env}) + \mathrm{size}(\mathrm{kont})$. Then there is a cost $s$ with
--
--   $$ s \le (S+1)(S+30) + 100 \quad\text{and}\quad \texttt{stepEvProg}\ \text{on the input}\ \texttt{cons}(\mathrm{toData}(p), \texttt{cons}(\mathrm{env}, \mathrm{kont}))\ \text{halts with}\ \mathrm{stepEv}(\mathrm{toData}(p), \mathrm{env}, \mathrm{kont})\ \text{at cost}\ s. $$
--
--   Together with its counterpart for "return" controls (`stepRetProg_runs_cons`), this gives the step program `stepProg` of the self-interpreter (`stepProg_runs`), whose iteration is the efficient universal machine of the toolkit: the quadratic bound per step, applied to configurations of size polynomial in the simulated run, is what makes the universal machine's overhead polynomial.
--
--   **Formalization Note**. The bound is the function `stepEvBound S = (S + 1) * (S + 30) + 100` of `MIPRE.Cost.Machine`, and the conclusion is `stepEvProg.Runs (cons p.toData (cons env kont)) (stepEv p.toData env kont) s`, a run in the one-entry environment; $|p|$ is `esize p`, the size of the tree encoding `Prog.toData p`. The result is stated through the data-level step `stepEv` of `Cost/MachineData.lean` rather than the machine's `step`; the two agree on encoded configurations (`stepData_toData`), which `stepProg_runs` uses. The quadratic term comes only from the environment walk in the `var` and `elim` cases; all other cases are linear in $S$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Interpreter.lean#L414-L519; internal lemma of the formalization of blueprint lem:universal-tm (the evaluate half of the self-interpreter's step program)

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

theorem MIPRE.Cost.Machine.stepEvProg_runs (p : Prog) (env kont : Data) :
    ∃ s ≤ stepEvBound (esize p + env.size + kont.size),
      stepEvProg.Runs (.cons p.toData (.cons env kont)) (stepEv p.toData env kont) s := by sorry
