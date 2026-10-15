-- Prove2me | Theorems.Thm_MIPRE_Cost_kleeneFix_runs_of
-- name    : MIPRE.Cost.kleeneFix_runs_of
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:28:54.813674+00:00
-- url     : https://prove2.me/theorems/563c8476-2b25-4de9-afce-b583de563fb7
-- title:
--   Explicit time transfer of the Kleene fixed point $e = \mathrm{kleeneFix}(U,F)$: runs of $F(e)$ bound runs of $e$
-- statement:
--   Programs of the ambient cost model (`Prog`) read their input as variable $0$ and are *closed* (`WellScoped 1`) when they read no other variable; $p(x) \Downarrow_t r$ (`p.Runs x r t`) says that $p$ run on the input $x$ halts with result $r$ at cost $t$ in the timed big-step semantics, and $\mathrm{size}(v)$ is the number of nodes of a datum $v$. Programs are encoded as data by their tree serialization $\mathrm{enc}(p)$, with $|p| := \mathrm{size}(\mathrm{enc}(p))$ (`esize`), and $s(p, d) = \mathtt{let}\ \mathtt{cons}(\mathtt{const}\ d, \mathtt{var}\ 0)\ \mathtt{in}\ p$ (`hardcode p d`) is the s-m-n map, running $p$ on the pair of the literal $d$ and its input. A *universal machine* $U = (u, P_U)$ (`UniversalMachine`) is a closed program $u$ with a polynomial $P_U \in \mathbb{N}[X]$ such that (i) whenever $c(v) \Downarrow_t r$ there is $t' \le P_U(|c| + \mathrm{size}(v) + t)$ with $u(\mathtt{cons}(\mathrm{enc}(c), v)) \Downarrow_{t'} r$ (`time_le`), and (ii) whenever $u(\mathtt{cons}(\mathrm{enc}(c), v)) \Downarrow_{t'} r$ there is $t$ with $c(v) \Downarrow_t r$ (`halts_of`). A *polynomial-time map on programs* $F$ (`PolyTimeFun Prog Prog`) is a function $F : \mathrm{Prog} \to \mathrm{Prog}$ with a closed program $\mathrm{code}_F$ and an explicit polynomial $T_F$ such that $\mathrm{code}_F(\mathrm{enc}(x)) \Downarrow_{t} \mathrm{enc}(F(x))$ for some $t \le T_F(|x|)$, for every $x$.
--
--   The two-argument program of the fixed-point construction is $G = \mathrm{kleeneProg}(u, F)$ (`kleeneProg`): on an input $\mathtt{cons}(\mathrm{enc}(x), v)$ it forms the pair $(\mathrm{enc}(x), \mathrm{enc}(x))$, applies the s-m-n program `smnProg` to obtain $\mathrm{enc}(s(x, \mathrm{enc}(x)))$, applies $\mathrm{code}_F$ to obtain $\mathrm{enc}(F(s(x, \mathrm{enc}(x))))$, pairs the result with $v$ and runs $u$ on that pair. The *fixed point of $F$ through $U$* is
--
--   $$ e := \mathrm{kleeneFix}(U, F) = s\bigl(G, \mathrm{enc}(G)\bigr) \qquad\text{(`kleeneFix U F`)}, $$
--
--   and the fixed part of its overhead is the number (`kleeneOverhead U F`)
--
--   $$ \mathrm{kleeneOverhead}(U, F) := 7|G| + |e| + T_F(|e|) + 2|F(e)| + 60 . $$
--
--   **Statement.** If $F(e)(v) \Downarrow_t r$, then there is a cost $t'$ with $e(v) \Downarrow_{t'} r$ and
--
--   $$ t' \;\le\; P_U\bigl(\mathrm{size}(v) + t + |F(e)|\bigr) + 3\,\mathrm{size}(v) + \mathrm{kleeneOverhead}(U, F) . $$
--
--   This is the quantitative core of the efficient Kleene recursion theorem (blueprint `lem:kleene`, [MNY, Lemma 2.3]); `efficient_fixed_point` packages the right-hand side into a single polynomial in $\mathrm{size}(v) + t$. The construction and its overhead are exposed as definitions (`kleeneFix`, `kleeneOverhead`) because the polynomial-time halting reduction needs the overhead of the fixed point of a *family* of maps $F_M$ to be bounded uniformly in $M$, which only the explicit form shows.
--
--   **Formalization Note**: The overhead decomposes as the universal machine's polynomial at the argument $\mathrm{size}(v) + t + |F(e)|$; $3\,\mathrm{size}(v)$ for the three copies of the input made along the way (by the hardcoding prefix, the final pairing and the call of $u$); and the constant $\mathrm{kleeneOverhead}(U,F)$, which gathers seven copies of $\mathrm{enc}(G)$ ($|G|$ each), the time $T_F(|e|)$ of computing $F(e)$ from $\mathrm{enc}(e)$, two copies of $\mathrm{enc}(F(e))$ and $60$ units of rule costs. Only this direction — runs of $F(e)$ bound runs of $e$ — is formalized; see `efficient_fixed_point` for the departure from [MNY].
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Kleene.lean#L182-L201; blueprint lem:kleene, https://vidick.github.io/MIPRE-formalization/blueprint/; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 2.3

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
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Kleene

open MIPRE
open MIPRE.Cost
open Polynomial

theorem MIPRE.Cost.kleeneFix_runs_of (U : UniversalMachine) (F : PolyTimeFun Prog Prog) {v r : Data}
    {t : ℕ} (h : (F (kleeneFix U F)).Runs v r t) :
    ∃ t' ≤ U.bound.eval (v.size + t + esize (F (kleeneFix U F))) + 3 * v.size +
        kleeneOverhead U F,
      (kleeneFix U F).Runs v r t' := by sorry
