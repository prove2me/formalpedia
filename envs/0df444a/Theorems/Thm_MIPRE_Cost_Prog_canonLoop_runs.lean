-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_canonLoop_runs
-- name    : MIPRE.Cost.Prog.canonLoop_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:32:13.78184+00:00
-- url     : https://prove2.me/theorems/f436b7a3-1ae7-46aa-adcd-1e73dad8f162
-- title:
--   The canonicity loop computes the walk within cost linear in the list length times the state size
-- statement:
--   Programs of the ambient cost model (`Prog`) use de Bruijn variables, and `Eval env p r t` is the timed big-step semantics: in the environment $\mathit{env}$ (a list of data, variable $0$ first) the program $p$ halts with result $r$ at cost $t$, one unit per evaluation rule plus the size of every value read. The construct $\mathtt{loop}(b)$ iterates $b$ on the state held in variable $0$: $b$ returns $\mathtt{cons}(\mathit{flag}, s')$, and the loop stops with result $s'$ if $\mathit{flag} = \mathtt{nil}$ and continues with state $s'$ otherwise (a body result $\mathtt{nil}$ stops with $\mathtt{nil}$). $\mathrm{canonBody}$ is the fixed program of the module that performs one step of the canonicity walk on a state $\mathtt{cons}(\mathit{rest}, \mathit{last})$. For a datum $d$, $\mathrm{size}(d)$ counts its nodes ($\mathtt{nil}$ counting one) and $\mathrm{spine}(d)$ is the length of its right spine, the length of $d$ read as a list; a Boolean is encoded as $\mathsf{false} \mapsto \mathtt{nil}$, $\mathsf{true} \mapsto \mathtt{cons}(\mathtt{nil}, \mathtt{nil})$.
--
--   Let $d$ be a datum, $\mathit{last}$ a Boolean, $\mathit{env}$ any environment and $S \in \mathbb N$ with $\mathrm{size}(d) + 3 \le S$. Then
--
--   $$ \exists\, t \le (\mathrm{spine}(d) + 1)\,(S + 21):\qquad \mathrm{Eval}\bigl(\mathtt{cons}(d, \mathrm{encode}(\mathit{last})) :: \mathit{env},\ \ \mathtt{loop}(\mathrm{canonBody}),\ \ \mathrm{encode}(\mathrm{canonWalk}(d, \mathit{last})),\ \ t\bigr). $$
--
--   The bound has the shape budget times size that the format checks of the wrapper decider need (`Decider.TimeBoundAt` charges $T \cdot (|\text{input}| + 1)$), the budget here being the number of list elements walked. It is the loop inside `normBinProg`, whose cost bound `normBinProg_runs` is assembled from it.
--
--   **Formalization Note**. The statement is `MIPRE.Cost.Prog.canonLoop_runs`. The loop runs in the environment `Data.cons d (encode last) :: env` with an arbitrary tail `env`, and the result is `encode (canonWalk d last)`, the encoded Boolean of `Data.canonWalk`. The parameter `S` is any upper bound on `d.size + 3`, so that the cost can be bounded by a quantity fixed before the walk; the bound is `(d.spine + 1) * (S + 21)` with `Data.spine` the right-spine length, which the docstring writes as $(|d| + 1)(S + 21)$. The cost `t` is existentially quantified.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Lists.lean#L551-L584; internal lemma of the format-check programs of the wrapper decider (module docstring); no blueprint label is attached to this declaration

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
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

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.canonLoop_runs (d : Data) (last : Bool) (env : Env) (S : ℕ) (hS : d.size + 3 ≤ S) :
    ∃ t ≤ (d.spine + 1) * (S + 21),
      Eval (Data.cons d (encode last) :: env) (.loop canonBody) (encode (canonWalk d last)) t := by sorry
