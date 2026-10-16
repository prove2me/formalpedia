-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_parseLoop_runs
-- name    : MIPRE.Cost.Prog.parseLoop_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:38:26.678989+00:00
-- url     : https://prove2.me/theorems/1bb5e621-0ea5-44b2-97ac-2d6eb96efc1e
-- title:
--   The parsing loop of `parseProg` computes the top of the final stack of the stack machine, in time $(|x| + 1)(S + 21)$
-- statement:
--   Ambient cost model: data are binary trees (`Data`, $\mathrm{size}$ the number of nodes), programs have de Bruijn variables, an environment $\rho$ is a list of data (variable $i$ reads the $i$-th entry), and $\mathrm{Eval}\ \rho\ p\ r\ t$ is the timed big-step relation: in $\rho$, the program $p$ halts with result $r$ at cost $t$. A list of data $s$ is the datum $\mathrm{list}(s)$, a $\mathtt{cons}$-chain ending in $\mathtt{nil}$; a bit string encodes as a $\mathtt{cons}$-chain of bits. Description strings are postorder serializations of data, read back by a stack machine: a $0$ pushes $\mathtt{nil}$, a $1$ pops two entries and pushes their pair (a stack with fewer than two entries is left alone); `stackRun x s` is the stack after running the machine over $x$ from the stack $s$. The program `parseBody` is the loop body of the reader, on a state $\mathtt{cons}(\text{bits}, \text{stack})$: at the end of the input it stops with the top of the stack ($\mathtt{nil}$ for an empty stack); otherwise it performs one step of the stack machine on the first bit and continues on the remaining bits.
--
--   Let $x$ be a bit string, $s$ a list of data, $\rho$ an environment and $S \in \mathbb N$ with $\mathrm{size}(\mathrm{encode}\ x) + \mathrm{size}(\mathrm{list}\ s) + 2|x| \le S$. Then
--
--   $$ \exists\, t \le (|x| + 1)(S + 21):\qquad \mathrm{Eval}\ \bigl(\mathtt{cons}(\mathrm{encode}\ x, \mathrm{list}\ s) :: \rho\bigr)\ (\mathtt{loop}\ \mathrm{parseBody})\ \bigl(\mathrm{head}_{\mathtt{nil}}(\mathrm{stackRun}(x, s))\bigr)\ t . $$
--
--   The loop started on the state (remaining bits, current stack) halts with the top of the final stack, within a cost linear in $|x|$ times the size parameter $S$, which dominates the sizes along the run. This is the loop invariant of `parseProg_runs`, the reader with which the compressor's decider reads the description it is handed.
--
--   **Formalization Note**. The theorem is `MIPRE.Cost.Prog.parseLoop_runs (x : BitStr) (s : List Data) (env : Env) (S : ℕ) (hS : (encode x : Data).size + (list s).size + 2 * x.length ≤ S)`. `Env` is `List Data`, `Data.list` the `cons`-chain of a list, `.loop parseBody` the loop construct of `Prog`, and `(stackRun x s).headD Data.nil` is `List.headD` with default $\mathtt{nil}$ (`Data.parse x` is the case $s = [\,]$). The bound has the shape (iterations + 1) times (size parameter + constant) used throughout the loop library, the constant $21$ absorbing the per-step cost of `parseBody`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Serial.lean#L169-L198; internal lemma of the formalization of the halting reduction (the reader of description strings, in the ambient model)

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Serial

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.parseLoop_runs (x : BitStr) (s : List Data) (env : Env) (S : ℕ)
    (hS : (encode x : Data).size + (list s).size + 2 * x.length ≤ S) :
    ∃ t ≤ (x.length + 1) * (S + 21),
      Eval (Data.cons (encode x) (list s) :: env) (.loop parseBody) ((stackRun x s).headD Data.nil) t := by sorry
