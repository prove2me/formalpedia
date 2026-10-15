-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_dispatch_runs
-- name    : MIPRE.Cost.Machine.dispatch_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:27:20.898162+00:00
-- url     : https://prove2.me/theorems/0b1bd7df-624b-4209-a985-7f9efb5bd9b5
-- title:
--   Tag dispatch over closed programs costs the called program's time plus $\mathrm{size}(p_k) + k + 3$
-- statement:
--   We work in the ambient cost model of the formalization: data are binary trees (`Data`, from `nil` and `cons`), $\mathrm{size}(d)$ is the number of nodes of $d$, and $\mathrm{Eval}(\mathrm{env}, p, r, t)$ is the timed semantics (the program $p$ in the environment $\mathrm{env}$ halts with $r$ at cost exactly $t$; one unit per rule, plus the size of every value read by a variable or literal). The self-interpreter implements, as a program, the step function of a small-step evaluation machine whose configurations are encoded as data: an environment is a `cons`-chain of values, a stack a `cons`-chain of encoded frames, and a program $p$ is its tree encoding $\mathrm{toData}(p)$, a unary tag ($0$ to $6$ for `var`, `nil`, `cons`, `elim`, `let_`, `loop`, `const`) paired with the fields.
--
--   The interpreter selects the case program for a step by the tag of the program or frame at hand, a unary numeral. For a list of closed programs $cs = [c_0, \dots, c_{\ell-1}]$ and variable indices $i, \mathit{idx}$, the dispatcher $\mathrm{dispatch}(cs, i, \mathit{idx})$ is a chain of `elim`s on variable $i$: it calls $c_0$ on the value of variable $\mathit{idx}$ if that numeral is $0$, and otherwise recurses on the tail of the list, with the index of the numeral now $1$ and the index of the argument shifted by $2$ (each `elim` on a `cons` binds two more variables); the last program of the list is called unconditionally. Calling a closed program $c$ on variable $v$ is $\mathrm{callVar}(v, c) = \texttt{let\_}\,(\texttt{var}\,v)\ c$.
--
--   Let $cs$ be a list of programs that are all well-scoped in a one-entry environment (closed), let $k < |cs|$, and let $E$ be an environment whose variable $i$ holds the unary numeral $\mathrm{ofNat}(k)$ and whose variable $\mathit{idx}$ holds the value $p_k$. Suppose that $c_k$, run on the input $p_k$, halts with result $r$ at cost $t$. Then there is a cost $s$ with
--
--   $$ s \le t + \mathrm{size}(p_k) + k + 3 \quad\text{and}\quad \mathrm{Eval}\bigl(E,\ \mathrm{dispatch}(cs, i, \mathit{idx}),\ r,\ s\bigr). $$
--
--   This is the generic lemma behind the two step programs of the self-interpreter: `stepEvProg` dispatches over the seven case programs of "evaluate" by the tag of the program, and `stepRetProg` over the four case programs of "return" by the tag of the top frame.
--
--   **Formalization Note**. The statement quantifies over the list `cs : List Prog` and the indices explicitly, as the recursion on the list requires (`MIPRE.Cost.Machine.dispatch` is defined by cases `[]`, `[c]`, `c :: c' :: cs`). The hypothesis on $c_k$ is `Eval [pk] (cs.getD k .nil) r t`, a run in the one-entry environment; the overhead $\mathrm{size}(p_k) + k + 3$ is one copy of the argument ($\mathrm{size}(p_k)+1$), one unit per `elim` passed ($k$, or $k+1$ when the chain has not yet reached its last element), and the units of the `let_` and `var` of the call.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Interpreter.lean#L348-L366; internal lemma of the formalization of blueprint lem:universal-tm (the tag dispatch of the self-interpreter's step programs)

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

theorem MIPRE.Cost.Machine.dispatch_runs : ∀ (cs : List Prog) (k i idx : ℕ) (E : Env) (pk r : Data) (t : ℕ),
    k < cs.length → (∀ c ∈ cs, c.WellScoped 1) → E.get i = Data.ofNat k → E.get idx = pk →
    Eval [pk] (cs.getD k .nil) r t →
    ∃ s ≤ t + pk.size + k + 3, Eval E (dispatch cs i idx) r s := by sorry
